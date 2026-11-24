-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rabinowitschEval_rename_ff6a73805728
-- name    : P2M_GroundTheory_Heights__Heights_rabinowitschEval_rename_ff6a73805728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:26.420934+00:00
-- url     : https://prove2.me/theorems/df54c2c4-089b-4bfd-895b-94ddd518f3bc
-- title:
--   P2 M Ground Theory Heights  Heights rabinowitsch Eval rename ff6a73805728: P2 M Ground Theory Heights  Heights rabinowitsch Eval rename ff6a73805728
-- statement:
--   The P2 M Ground Theory Heights  Heights rabinowitsch Eval rename ff6a73805728 construction uses the P2 M Ground Theory Heights  Heights rabinowitsch Eval rename ff6a73805728 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L40-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_rabinowitschEval_rename_ff6a73805728 (K : Ideal (MvPolynomial ι R)) (g p : MvPolynomial ι R) :
    rabinowitschEval K g (rename some p) =
      algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rabinowitschEval_rename» := P2M_GroundTheory_Heights__Heights_rabinowitschEval_rename_ff6a73805728
