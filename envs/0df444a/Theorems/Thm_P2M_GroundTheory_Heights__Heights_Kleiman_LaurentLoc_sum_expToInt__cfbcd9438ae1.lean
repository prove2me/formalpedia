-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt__cfbcd9438ae1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt__cfbcd9438ae1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:29.019667+00:00
-- url     : https://prove2.me/theorems/3933a62a-b18a-41e0-b95a-35c98a8d12b7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc sum exp To Int  cfbcd9438ae1: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc sum exp To Int  cfbcd9438ae1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc sum exp To Int  cfbcd9438ae1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc sum exp To Int  cfbcd9438ae1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L140-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt__cfbcd9438ae1 (d : Fin (N + 1) →₀ ℕ) :
    ∑ j, expToInt N d j = ((Finsupp.weight (1 : Fin (N + 1) → ℕ) d : ℕ) : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«sum_expToInt'» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt__cfbcd9438ae1
