-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_conj_roots
-- name    : PI.GreenLabelMapW.conj_roots
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:49.828413+00:00
-- url     : https://prove2.me/theorems/f8815b16-4cb4-43af-8c36-70e9757b26a6
-- title:
--   Green Label Map W: conj roots
-- statement:
--   The Green Label Map W construction uses the conj roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L38-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/RootPowCard.lean#L38-L55

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

theorem PI.GreenLabelMapW.conj_roots {P : K[X]} (hm : P.Monic) (hi : Irreducible P) {w : AlgebraicClosure K}
    (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x)) (y : AlgebraicClosure K) :
    aeval y (minpoly K (f w)) = 0 ↔ ∃ r, aeval r P = 0 ∧ f r = y := by sorry
