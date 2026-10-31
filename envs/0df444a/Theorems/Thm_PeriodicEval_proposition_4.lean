-- Prove2me | Theorems.Thm_PeriodicEval_proposition_4
-- name    : PeriodicEval.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:05.506733+00:00
-- url     : https://prove2.me/theorems/bc261ae7-e597-4661-8262-d8d933ae7845
-- title:
--   Proposition 4 — $\Phi(a)=e^{-\beta\tau}F(a)$ is a contraction with a unique fixed point
-- statement:
--   Under the standing assumptions, $F(a)$ is finite for every $a\in\mathbb R$, and the map
--
--   $$\Phi(a):=e^{-\beta\tau}F(a)\qquad(24)$$
--
--   is a contraction on $(\mathbb R,|\cdot|)$, with Lipschitz constant $e^{-(\beta-h)\tau}<1$:
--
--   $$|\Phi(a_1)-\Phi(a_2)|\le e^{-(\beta-h)\tau}|a_1-a_2|.$$
--
--   Hence $\Phi$ has a unique fixed point $A^*=\Phi(A^*)$.
--
--   The fixed point $A^*$ is the constant of the value function $V(x)=A^*x^\alpha$ in Theorem 1, and it can be computed by iterating $\Phi$.
--
--   **Formalization Note** $F$ and $\Phi$ are extended-real valued; finiteness makes $\Phi$ a real map, as "contraction on $(\mathbb R,|\cdot|)$" presupposes.
--
--   Differences from the source:
--   - generalization: Φ is a contraction → Φ is a contraction with the explicit constant e^{−(β−h)τ}; reason: the constant is the one the proof derives (p.40); forgetting it gives the printed statement
--   - encoding: Φ : ℝ → ℝ → F(a) ≠ ±∞ for all a, and Φ read through EReal.toReal; reason: F is an extended-real supremum; finiteness is part of the claim
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), Proposition 4, eq. (24), pp.39–40, and its proof, p.40

import Mathlib
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PeriodicEval

/-- Proposition 4, SSRN 3971852 (June 20, 2023), pp.39–40: `Φ(a) := e^{−βτ}F(a)` (24) is a
contraction on `(ℝ, |·|)` and so admits a unique fixed point `A* = Φ(A*)`.

Stated as: `F(a)` is finite for every `a`; the real map `a ↦ Φ(a)` is a contraction with
Lipschitz constant `e^{−(β−h)τ} < 1` (the constant of the proof, p.40); and there is exactly
one real `A` with `Φ(A) = A`.

**Formalization Note** `F` and `Φ` are `EReal`-valued; finiteness makes `Φ` a map
`ℝ → ℝ` (via `EReal.toReal`), which is what "contraction on `(ℝ, |·|)`" presupposes. -/
theorem proposition_4 (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) :
    (∀ a : ℝ, F p P ℱ B a ≠ ⊤ ∧ F p P ℱ B a ≠ ⊥) ∧
    ContractingWith (Real.exp (-((p.β - p.h) * p.τ))).toNNReal
      (fun a : ℝ => (Φ p P ℱ B a).toReal) ∧
    ∃! A : ℝ, Φ p P ℱ B A = (A : EReal) := by sorry

end PeriodicEval
