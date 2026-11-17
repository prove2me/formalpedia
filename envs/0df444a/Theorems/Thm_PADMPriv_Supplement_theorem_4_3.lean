-- Prove2me | Theorems.Thm_PADMPriv_Supplement_theorem_4_3
-- name    : PADMPriv.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:50:48.239786+00:00
-- url     : https://prove2.me/theorems/649f0c1e-2072-44ca-8c0b-6f021ab200b6
-- title:
--   Theorem 4.3 — the $n$-th output of PADM-$L_\lambda$ is $(\alpha,2m\alpha C^2/(\lambda^2(n-i+1)))$-RDP for its $i$-th input
-- statement:
--   Assume Condition 1: there is $C>0$ such that $\|T_{f_k}(u)-T_{f'_k}(u)\|_2\le C$ for all neighbouring data sets $D\sim D'$, all steps $k$ and all $u\in\mathbb R^m$ (21). Let $f(\cdot,d)$ and $g$ be convex, $\beta>0$, $\lambda>0$, and run private PADM with independent noise vectors $z_{(k)}\sim L_m(0_m,\lambda)$, i.e. with independent $L(0,\lambda)$ coordinates (PADM-$L_\lambda$). Then for every $\alpha>1$, every record index $i\in\{1,\dots,n\}$ and every two data sets $D$, $D'$ that agree except possibly at record $i$,
--   $$
--   D_\alpha\big(\tilde u_{(n)}(D)\,\big\|\,\tilde u_{(n)}(D')\big)\le\frac{2m\alpha C^2}{\lambda^2(n-i+1)} .
--   $$
--   That is, the final output of PADM-$L_\lambda$ achieves $\big(\alpha,\frac{2m\alpha C^2}{\lambda^2(n-i+1)}\big)$-RDP for its $i$-th input: the Laplace mechanism also amplifies privacy by iteration, with the dimension $m$ entering the bound.
--
--   **Formalization Note** Records are indexed from $0$, so the index $i$ of the Lean statement is record $i+1$ and the denominator is $\lambda^2(n-i)$. The Laplace scale is called `s`. The proximal problems (13) are assumed to have minimizers. The encoding is that of the published Gaussian twin `PADMPriv.theorem_4_1`.
--
--   Differences from the source:
--   - encoding: (α, 2mαC²/(λ²(n − i + 1)))-RDP for the i-th input → the divergence bound for every two data sets agreeing outside record i; reason: this is Definition 3 restricted to neighbours that differ at record i
--   - encoding: 1-based record index i, denominator λ²(n − i + 1) → 0-based index i, denominator s²(n − i); reason: the same record and the same value
--   - encoding: Laplace noise L_m(0_m, λ) with λ > 0 (p.10) → lapNoise m s: the product of m copies of the published one-dimensional Laplace law of scale s, with hypothesis 0 < s; reason: the same law; the scale is renamed because λ is a Lean keyword
--   - encoding: the sample proximal operators P_{β,f(·,d),A} used as everywhere defined → hypothesis that (13) for f(·,d) has a minimizer for every record d and input u; reason: Algorithm 1 is undefined otherwise; excludes only undefined cases
--   - encoding: P_{β,g,B} used as everywhere defined → hypothesis that (13) for g has a minimizer at every input; reason: T_{f_k} is undefined otherwise; excludes only undefined cases
--   - encoding: the Rényi divergence of Definition 2 → computed through dP/dQ, +∞ when P is not absolutely continuous with respect to Q; reason: equal to Definition 2 for α > 1
--   - generalization: full row rank of A and B (standing assumption, p.6) → not assumed; reason: the statement and its proof use only convexity and the proximal minimizers, never V or U; the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Theorem 4.3, p.10 (proof A.10, p.26); Condition 1, p.9; Laplace mechanism, Section 4.3, p.10

import Mathlib
import Definitions.Def_PADMPriv_Supplement_padmLawLap
import Definitions.Def_PADMPriv_Adjacent
import Definitions.Def_PADMPriv_renyiDiv

namespace PADMPriv.Supplement

/-- Theorem 4.3 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly
Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.10 (proof
A.10, p.26): under Condition 1 (21) with constant `C > 0`, the final (`n`-th) output of PADM-L_λ
achieves `(α, 2mαC²/(λ²(n − i + 1)))`-RDP for its `i`-th input: for every `α > 1` and every two
data sets `D`, `D′` that differ at most in record `i`,
`D_α(ũ₍ₙ₎(D)‖ũ₍ₙ₎(D′)) ≤ 2mαC²/(λ²(n − i + 1))`.

**Formalization Note** The noise is `L_m(0_m, λ)` (`lapNoise`, independent `L(0, λ)` coordinates),
`λ > 0` (p.10); the scale is named `s`. Records are `Fin n`-indexed: index `i` is the paper's
record `i + 1`, so `n − (i + 1) + 1 = n − i`. Condition 1 (p.9) is stated literally. `f(·, d)` and
`g` are real-valued convex, `β > 0`, and the proximal problems (13) are assumed to have
minimizers, so that every `T_{f_k}` is defined (as in the published `PADMPriv.theorem_4_1`). -/
theorem theorem_4_3 {m p l n : ℕ} {R : Type*} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (hfconv : ∀ d, ConvexOn ℝ Set.univ (fun x => f x d)) (hg : ConvexOn ℝ Set.univ g)
    (β : ℝ) (hβ : 0 < β) (hfprox : ∀ d u, ∃ x, IsProxMin β (fun x => f x d) A u x)
    (hgprox : ∀ v, ∃ y, IsProxMin β g B v y) (C : ℝ) (hC : 0 < C)
    (hcond1 : ∀ D D' : Fin n → R, Adjacent D D' → ∀ (k : Fin n) (u : EuclideanSpace ℝ (Fin m)),
      ‖padmOp β (fun x => f x (D k)) g A B c u - padmOp β (fun x => f x (D' k)) g A B c u‖ ≤ C)
    (s : ℝ) (hs : 0 < s) (α : ℝ) (hα : 1 < α) (x₀ : EuclideanSpace ℝ (Fin p)) (i : Fin n)
    (D D' : Fin n → R) (hDD' : ∀ j, j ≠ i → D j = D' j) :
    renyiDiv α (padmLawLap β s f g A B c x₀ D n) (padmLawLap β s f g A B c x₀ D' n) ≤
      ((2 * m * α * C ^ 2 / (s ^ 2 * ((n : ℝ) - (i : ℕ))) : ℝ) : EReal) := by sorry

end PADMPriv.Supplement
