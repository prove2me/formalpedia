-- Prove2me | Theorems.Thm_PADMPriv_Supplement_theorem_4_4
-- name    : PADMPriv.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:51:29.627351+00:00
-- url     : https://prove2.me/theorems/6ef33916-2757-42b9-87d2-8ce44b8dbcda
-- title:
--   Theorem 4.4 — Stop-PADM-$L_\lambda$ is $(\alpha,2(e^2-1)m\alpha C^2\ln(en)/(n\lambda^2))$-RDP for $\lambda\ge C\sqrt{m\alpha(\alpha-1)}$
-- statement:
--   Assume Condition 1 (21) with constant $C>0$. Let $f(\cdot,d)$ and $g$ be convex, $\beta>0$ and $n\ge1$. Stop-PADM-$L_\lambda$ runs private PADM with independent $L_m(0_m,\lambda)$ noise vectors and outputs $\tilde u_{(K)}$, where $K$ is uniform on $\{\lfloor n/2\rfloor+1,\dots,n\}$ and independent of the noise. Then for every $\alpha>1$ and every scale $\lambda>0$ with
--   $$
--   \lambda\ge C\sqrt{m\alpha(\alpha-1)},
--   $$
--   Stop-PADM-$L_\lambda$ achieves $(\alpha,\varepsilon)$-RDP with
--   $$
--   \varepsilon=\frac{2(e^2-1)\,m\alpha C^2\ln(en)}{n\lambda^2}:
--   $$
--   for all neighbouring data sets $D\sim D'$ (differing in at most one record), $D_\alpha\big(\tilde u_{(K)}(D)\,\|\,\tilde u_{(K)}(D')\big)\le\varepsilon$.
--
--   Random stopping turns the per-record bound of Theorem 4.3 into a bound uniform over records that decays as $\ln(en)/n$.
--
--   **Formalization Note** The Laplace scale is called `s`; $\lambda>0$ is kept as a separate hypothesis since $\lambda\ge C\sqrt{m\alpha(\alpha-1)}$ does not force it at $m=0$. $\ln(en)$ is `Real.log (Real.exp 1 * n)`. The encoding is that of the published Gaussian twin `PADMPriv.theorem_4_2`.
--
--   Differences from the source:
--   - encoding: the random output with K uniform on {⌊n/2⌋+1, …, n} → n ≥ 1; reason: the window is empty at n = 0; n ≥ 1 is implicit
--   - encoding: Laplace noise L_m(0_m, λ) with λ > 0 (p.10) → lapNoise m s: the product of m copies of the published one-dimensional Laplace law of scale s, with hypothesis 0 < s; reason: the same law; the scale is renamed because λ is a Lean keyword
--   - encoding: the sample proximal operators P_{β,f(·,d),A} used as everywhere defined → hypothesis that (13) for f(·,d) has a minimizer for every record d and input u; reason: Algorithm 1 is undefined otherwise; excludes only undefined cases
--   - encoding: P_{β,g,B} used as everywhere defined → hypothesis that (13) for g has a minimizer at every input; reason: T_{f_k} is undefined otherwise; excludes only undefined cases
--   - encoding: the Rényi divergence of Definition 2 → computed through dP/dQ, +∞ when P is not absolutely continuous with respect to Q; reason: equal to Definition 2 for α > 1
--   - generalization: full row rank of A and B (standing assumption, p.6) → not assumed; reason: the statement and its proof use only convexity and the proximal minimizers, never V or U; the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Theorem 4.4, p.10 (proof A.11, pp.26–27); Condition 1, p.9

import Mathlib
import Definitions.Def_PADMPriv_Supplement_stopPadmLawLap
import Definitions.Def_PADMPriv_IsRDP

namespace PADMPriv.Supplement

/-- Theorem 4.4 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly
Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.10 (proof
A.11, pp.26–27): under Condition 1 (21) with constant `C > 0`, for any `α > 1` and
`λ ≥ C√(mα(α − 1))`, the random output `ũ₍K₎` of Stop-PADM-L_λ (`K` uniform on
`{⌊n/2⌋ + 1, …, n}`) achieves `(α, 2(e² − 1)mαC² ln(en)/(nλ²))`-RDP.

**Formalization Note** The noise is `L_m(0_m, λ)` (`lapNoise`) with `λ > 0` (p.10), kept as its
own hypothesis since `λ ≥ C√(mα(α − 1))` does not force it at `m = 0`; the scale is named `s`.
Condition 1 (p.9) is stated literally over neighbouring data sets. `f(·, d)`, `g` real-valued
convex, `β > 0`, `n ≥ 1` (the window is nonempty); the proximal problems (13) are assumed to have
minimizers, so that every `T_{f_k}` is defined. `ln(en)` is `Real.log (Real.exp 1 * n)`. -/
theorem theorem_4_4 {m p l n : ℕ} {R : Type*} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (hfconv : ∀ d, ConvexOn ℝ Set.univ (fun x => f x d)) (hg : ConvexOn ℝ Set.univ g)
    (β : ℝ) (hβ : 0 < β) (hfprox : ∀ d u, ∃ x, IsProxMin β (fun x => f x d) A u x)
    (hgprox : ∀ v, ∃ y, IsProxMin β g B v y) (C : ℝ) (hC : 0 < C)
    (hcond1 : ∀ D D' : Fin n → R, Adjacent D D' → ∀ (k : Fin n) (u : EuclideanSpace ℝ (Fin m)),
      ‖padmOp β (fun x => f x (D k)) g A B c u - padmOp β (fun x => f x (D' k)) g A B c u‖ ≤ C)
    (α : ℝ) (hα : 1 < α) (s : ℝ) (hs : 0 < s) (hsC : C * Real.sqrt (m * α * (α - 1)) ≤ s)
    (x₀ : EuclideanSpace ℝ (Fin p)) :
    IsRDP α (2 * (Real.exp 2 - 1) * m * α * C ^ 2 * Real.log (Real.exp 1 * n) / (n * s ^ 2))
      (fun D : Fin n → R => stopPadmLawLap β s f g A B c x₀ D) := by sorry

end PADMPriv.Supplement
