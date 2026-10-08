-- Prove2me | Theorems.Thm_PDASNewton_FunSpace_active_sets_coincide
-- name    : PDASNewton.FunSpace.active_sets_coincide
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:12.619979+00:00
-- url     : https://prove2.me/theorems/aabfc8a8-75ab-41f1-8b76-23d108b834d8
-- title:
--   Proof of Theorem 4.1, pp. 22–23 — with c = β and λ⁰ = f − Ay⁰, λᵏ + β(yᵏ − ψ) = f − Cyᵏ − βψ for all k ≥ 0
-- statement:
--   Let $(\Omega, \mu)$ be a finite measure space, $q > 2$, $\beta > 0$, $C \in \mathcal{L}(L^2(\Omega), L^q(\Omega))$, and $A = C + \beta I$ as in (H2). Let $f, \psi \in L^2(\Omega)$ and let $(y^k, \lambda^k)_{k \ge 0}$ be a run of the primal-dual active set algorithm in $L^2(\Omega)$ with $c = \beta$, started from $\lambda^0 = f - Ay^0$. Then for every $k \ge 0$, almost everywhere,
--   $$\lambda^k + \beta(y^k - \psi) = f - Cy^k - \beta\psi .$$
--   Consequently the active sets $\mathcal{A}_k = \{\lambda^k + \beta(y^k - \psi) > 0\}$ are those of the reduced algorithm, $\{f - Cy^k - \beta\psi > 0\}$, for every $k$, including $k = 0$.
--
--   This is the first step of the proof of Theorem 4.1: the algorithm in the two variables $(y, \lambda)$ produces the same primal iterates as the reduced algorithm in $y$ alone.
--
--   **Formalization Note** The page states Theorem 4.1 with $\lambda^0 = \beta(y^0 - \psi)$, but its proof uses "due to our choice of $\lambda^0$ and $\beta = c$ we have $\lambda^0 + \beta(y^0 - \psi) = f - Cy^0 - \beta\psi$", which holds exactly when $\lambda^0 = f - Cy^0 - \beta y^0 = f - Ay^0$. This item uses that initialization. For $k \ge 1$ the identity follows from step (iii) whatever $\lambda^0$ is.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, pp. 22–23, Appendix A, proof of Theorem 4.1, first paragraph

import Mathlib
import Definitions.Def_PDASNewton_FunSpace_Setting

namespace PDASNewton.FunSpace

open MeasureTheory
open scoped ENNReal

/-- Proof of Theorem 4.1, pp. 22–23: under (H2), along a run of the `L²` algorithm with `c = β`
started from `λ⁰ = f - A y⁰`, `λᵏ + β (yᵏ - ψ) = f - C yᵏ - β ψ` a.e. for every `k ≥ 0`; hence
`𝓐_k = {f - C yᵏ - β ψ > 0}` is the active set of the reduced algorithm. -/
theorem active_sets_coincide {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 2 < q)
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (β : ℝ) (hβ : 0 < β) (C : Lp ℝ 2 μ →L[ℝ] Lp ℝ q μ)
    (hAC : ∀ y : Lp ℝ 2 μ, (A y : α → ℝ) =ᵐ[μ] fun x => C y x + β * y x)
    (f ψ : Lp ℝ 2 μ) (y lam : ℕ → Lp ℝ 2 μ) (hrun : IsRun A f ψ β y lam)
    (hinit : lam 0 = f - A (y 0)) :
    ∀ k, ∀ᵐ x ∂μ, lam k x + β * (y k x - ψ x) = f x - C (y k) x - β * ψ x := by sorry

end PDASNewton.FunSpace
