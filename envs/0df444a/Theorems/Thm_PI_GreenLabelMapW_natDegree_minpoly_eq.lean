-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_natDegree_minpoly_eq
-- name    : PI.GreenLabelMapW.natDegree_minpoly_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:37.572799+00:00
-- url     : https://prove2.me/theorems/0082dcdc-28c6-4cca-94e6-8b75cb4a181c
-- title:
--   Green Label Map W: nat Degree minpoly eq
-- statement:
--   The Green Label Map W construction uses the nat Degree minpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L83-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K]

theorem PI.GreenLabelMapW.natDegree_minpoly_eq {P : K[X]} (hm : P.Monic) (hi : Irreducible P)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x))
    (hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ P = 0 → aeval r₂ P = 0 → f r₁ = f r₂ → r₁ = r₂) :
    (minpoly K (f w)).natDegree = P.natDegree := by sorry
