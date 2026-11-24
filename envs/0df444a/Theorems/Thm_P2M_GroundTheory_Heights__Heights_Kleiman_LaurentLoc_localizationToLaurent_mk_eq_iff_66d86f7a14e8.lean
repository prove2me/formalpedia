-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:57.254211+00:00
-- url     : https://prove2.me/theorems/0e7c6945-ebca-4fd2-9236-685f4d011e43
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent mk eq iff 66d86f7a14e8: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent mk eq iff 66d86f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent mk eq iff 66d86f7a14e8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent mk eq iff 66d86f7a14e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L102-L107

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
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8 (I : Finset (Fin (N + 1))) (p : Poly S N) (s : monos (S := S) I) (y : LRing S N) :
    iotaP I (LocalizedModule.mk p s) = y ↔ toL S N p = toL S N s * y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«localizationToLaurent_mk_eq_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_eq_iff_66d86f7a14e8
