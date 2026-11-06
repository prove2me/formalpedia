-- Prove2me | Theorems.Thm_PADMPriv_theorem_4_2
-- name    : PADMPriv.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:11:59.116801+00:00
-- url     : https://prove2.me/theorems/e00737ab-18c6-4ea9-a4ba-aa97fb4186bf
-- title:
--   Theorem 4.2 — Stop-PADM-$N_\sigma$ is $(\alpha,2(e^2-1)\alpha C^2\ln(en)/(n\sigma^2))$-RDP for $\sigma\ge C\sqrt{\alpha(\alpha-1)}$
-- statement:
--   Assume Condition 1 with constant $C>0$ (as in Theorem 4.1), $f(\cdot,d)$ and $g$ convex and $\beta>0$. For any $\alpha>1$ and $\sigma\ge C\sqrt{\alpha(\alpha-1)}$, the random output $\tilde u_{(K)}$ of Stop-PADM-$N_\sigma$, with $K$ uniform on $\{\lfloor n/2\rfloor+1,\dots,n\}$, achieves
--   $$
--   \Big(\alpha,\ \frac{2(e^2-1)\alpha C^2\ln(en)}{n\sigma^2}\Big)\text{-RDP}.
--   $$
--
--   Random stopping replaces the record-dependent guarantee of Theorem 4.1 by a uniform one of order $\ln(en)/n$.
--
--   **Formalization Note** $n\ge1$. The proximal problems (13) are assumed to have minimizers.
--
--   Differences from the source:
--   - encoding: the sample proximal operators P_{β,f(·,d),A} used as everywhere defined → hypothesis that (13) for f(·,d) has a minimizer for every record d and input u; reason: Algorithm 1 is undefined otherwise; excludes only undefined cases
--   - encoding: P_{β,g,B} used as everywhere defined → hypothesis that (13) for g has a minimizer at every input; reason: T_{f_k} is undefined otherwise; excludes only undefined cases
--   - encoding: a sample horizon n → n ≥ 1; reason: the stopping window is empty for n = 0
--   - encoding: the Rényi divergence of Definition 2 → computed through dP/dQ, +∞ when P is not absolutely continuous with respect to Q; reason: equal to Definition 2 for α > 1
--   - generalization: full row rank of A and B (standing assumption, p.6) → not assumed; reason: the statement and its proof use only convexity and the proximal minimizers, never V or U; the source's case is an instance
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Theorem 4.2, p.10 (proof A.8, pp.24–25)

import Mathlib
import Definitions.Def_PADMPriv_stopPadmLaw
import Definitions.Def_PADMPriv_IsRDP

namespace PADMPriv

/-- Theorem 4.2 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.10 (proof A.8, pp.24–25): under Condition 1 (21) with
constant `C > 0`, for any `α > 1` and `σ ≥ C√(α(α − 1))`, the random output `ũ₍K₎` of
Stop-PADM-N_σ (`K` uniform on `{⌊n/2⌋ + 1, …, n}`) achieves
`(α, 2(e² − 1)αC² ln(en)/(nσ²))`-RDP.

**Formalization Note** Condition 1 (p.9) is stated literally over neighbouring data sets.
`f(·, d)`, `g` real-valued convex, `β > 0`, `n ≥ 1` (the window is nonempty); the proximal
problems (13) are assumed to have minimizers, so that every `T_{f_k}` is defined. `ln(en)` is
`Real.log (Real.exp 1 * n)`. -/
theorem theorem_4_2 {m p l n : ℕ} {R : Type*} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (c : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (g : EuclideanSpace ℝ (Fin l) → ℝ)
    (hfconv : ∀ d, ConvexOn ℝ Set.univ (fun x => f x d)) (hg : ConvexOn ℝ Set.univ g)
    (β : ℝ) (hβ : 0 < β) (hfprox : ∀ d u, ∃ x, IsProxMin β (fun x => f x d) A u x)
    (hgprox : ∀ v, ∃ y, IsProxMin β g B v y) (C : ℝ) (hC : 0 < C)
    (hcond1 : ∀ D D' : Fin n → R, Adjacent D D' → ∀ (k : Fin n) (u : EuclideanSpace ℝ (Fin m)),
      ‖padmOp β (fun x => f x (D k)) g A B c u - padmOp β (fun x => f x (D' k)) g A B c u‖ ≤ C)
    (α : ℝ) (hα : 1 < α) (σ : ℝ) (hσ : C * Real.sqrt (α * (α - 1)) ≤ σ)
    (x₀ : EuclideanSpace ℝ (Fin p)) :
    IsRDP α (2 * (Real.exp 2 - 1) * α * C ^ 2 * Real.log (Real.exp 1 * n) / (n * σ ^ 2))
      (fun D : Fin n → R => stopPadmLaw β σ f g A B c x₀ D) := by sorry

end PADMPriv
