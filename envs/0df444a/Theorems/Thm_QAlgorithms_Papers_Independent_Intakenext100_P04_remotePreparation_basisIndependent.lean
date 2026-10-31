-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P04_remotePreparation_basisIndependent
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P04.remotePreparation_basisIndependent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:48:37.659032+00:00
-- url     : https://prove2.me/theorems/0d785d1c-7868-4cae-9a29-9c24d4f0908f
-- title:
--   Local auxiliary measurement constructs a basis-independent source
-- statement:
--   Let $\rho_{AA'}$ be any positive trace-class density operator on an arbitrary complete bipartite complex Hilbert space. Independently choose $a\in\{0,1\}$ uniformly and perform any normalized two-outcome measurement $\{M_{a,g}\}_{g=0,1}$ on $A'$ alone. Construct the subnormalized emitted branches and their weights by
--
--   $$
--   B_{a,g}=\tfrac12\operatorname{Tr}_{A'}[(I\otimes\sqrt{M_{a,g}})\rho_{AA'}(I\otimes\sqrt{M_{a,g}})],\qquad p_{a,g}=\operatorname{Tr}B_{a,g}.
--   $$
--
--   The joint branches before partial trace are positive trace-class operators. Their weights are nonnegative, $\sum_g p_{a,g}=1/2$, and
--
--   $$
--   \sum_g B_{0,g}=\sum_g B_{1,g}=\tfrac12\operatorname{Tr}_{A'}\rho_{AA'}.
--   $$
--
--   Thus the constructed ensemble satisfies the source's weighted basis-independence condition. Zero-probability outcomes cause no division by zero, and the bit need not be unbiased.
--
--   **Formalization Note** A product Hilbert basis and the coefficient identity for $I_A\otimes M_{a,g}$ express locality without a finite-dimensional restriction. The local measurement's reduced branch is independent of the chosen realization of its instrument.
-- source:
--   Secure quantum key distribution with an uncharacterized source, arXiv:quant-ph/0208155v2, PDF p. 2, Source-design paragraph preceding Protocol 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P04

noncomputable section

universe u v w

namespace QAlgorithms.Papers.Independent.Intakenext100.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Advance50.P18 (keyEntropy)

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Koashi–Preskill PDF p.2, source design preceding Protocol 1: local
measurement of a fixed joint state supplies Eq.(1), with its actual branch
weights, without characterizing either the joint state or the two measurements. -/
theorem remotePreparation_basisIndependent {I : Type v} {J : Type w}
    (b : HilbertBasis (I × J) ℂ H) (rho : State b)
    (M : Bool → AuxiliaryMeasurement b) :
    (∀ a g, IsTraceClass (preparationBranch rho (M a) g) ∧
      IsPositive (preparationBranch rho (M a) g)) ∧
    (∀ a g, 0 ≤ preparationWeight rho (M a) g) ∧
    (∀ a, ∑ g, preparationWeight rho (M a) g = 1 / 2) ∧
    (∀ a, ∑ g, weightedEmittedBranch rho (M a) g =
      (1 / 2 : ℂ) • emittedMarginal b rho.val.val) ∧
    (∑ g, weightedEmittedBranch rho (M false) g) =
      ∑ g, weightedEmittedBranch rho (M true) g := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P04

end
