-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_constrainedHolevoAdditivity
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.constrainedHolevoAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:33:50.729993+00:00
-- url     : https://prove2.me/theorems/c699f94d-8881-4d57-ac24-348081705778
-- title:
--   §IV.1, (56)–(57): constrained Holevo additivity
-- statement:
--   Let $a\mapsto S_a$ be a memoryless trace-class c-q alphabet, let $f(a)\ge0$ be its letter cost, and let the finite budget $E$ admit a discrete probability law of expected cost at most $E$. Let $\bar C_n$ optimize the block Holevo information over all word laws whose ensemble-average total cost is at most $nE$, and let $\bar C_1=\sup_{\pi:\,\sum_a\pi_af(a)\le E}\Delta H(\pi)$. Then
--
--   $$\bar C_n=n\bar C_1\quad(n\ge1),\qquad \bar C=\bar C_1.$$
--
--   The source proof averages the marginals; no individual marginal is assumed to satisfy the one-letter budget. The statement permits infinite Holevo information and is separate from the per-word coding constraint.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 18, §IV.1, (56)–(57): constrained Holevo additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Equations (56)-(57), PDF pp.18-19. Only the average of the marginals
must satisfy the budget; no individual marginal constraint is assumed. -/
theorem constrainedHolevoAdditivity {A I : Type} [Nonempty A] [Nonempty I]
    (S : A → Matrix I I ℂ) (hS : ∀ a, TC.IsDensity (S a))
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (E : ℝ)
    (hfeasible : ∃ pi : DiscreteInputLaw A, HasMeanCostBound f E pi) :
    (∀ n : ℕ, 0 < n → cqHolevoBlock S f E n =
      (n : ℝ≥0∞) * cqHolevoSingle S f E) ∧
    cqHolevoCapacity S f E = cqHolevoSingle S f E := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
