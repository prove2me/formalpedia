-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_constrainedCqCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.constrainedCqCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:34:34.873912+00:00
-- url     : https://prove2.me/theorems/a23f4a61-accb-4080-a884-8d1552bb9b57
-- title:
--   Theorem 4: discrete alphabet with per-word additive constraint
-- statement:
--   Let $a\mapsto S_a$ be normalized trace-class c-q signals with one finite uniform bound on individual entropies. Let $f\ge0$, let $E$ be a finite real budget, and suppose the class of discrete laws with expected cost at most $E$ is nonempty. Require every transmitted word $w$ of length $n$ separately to satisfy $\sum_kf(w_k)\le nE$. Then the operational uniform-average-error capacity satisfies
--
--   $$C=\sup_{\pi:\,\sum_a\pi_af(a)\le E}\Delta H(\pi).$$
--
--   The supremum and capacity may be infinite. No central-limit assertion or uniform mixture-entropy bound is imposed as a hypothesis. This is the constrained discrete-alphabet coding theorem.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 19, Theorem 4: discrete alphabet with per-word additive constraint

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

/-- Theorem 4, PDF pp.18-20: every codeword separately satisfies its additive
budget. No CLT condition or uniform mixture-entropy bound is assumed. -/
theorem constrainedCqCoding {A I : Type} [Nonempty A] [Nonempty I]
    (S : A → Matrix I I ℂ) (hS : ∀ a, TC.IsDensity (S a))
    (hentropy : BoundedLetterEntropy S) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a)
    (E : ℝ) (hfeasible : ∃ pi : DiscreteInputLaw A, HasMeanCostBound f E pi) :
    averageErrorCqCapacity S f E = cqHolevoSingle S f E := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
