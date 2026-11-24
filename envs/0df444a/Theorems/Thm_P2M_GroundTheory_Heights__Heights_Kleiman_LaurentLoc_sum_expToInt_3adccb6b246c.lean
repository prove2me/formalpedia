-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt_3adccb6b246c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt_3adccb6b246c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:52.899169+00:00
-- url     : https://prove2.me/theorems/b6c67b01-a5be-4c3f-8d8c-2a8ef2a0eeb0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc sum exp To Int 3adccb6b246c: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc sum exp To Int 3adccb6b246c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc sum exp To Int 3adccb6b246c construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc sum exp To Int 3adccb6b246c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L135-L138

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt_3adccb6b246c (d : Fin (N + 1) →₀ ℕ) :
    ∑ j, expToInt N d j = Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«sum_expToInt» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt_3adccb6b246c
