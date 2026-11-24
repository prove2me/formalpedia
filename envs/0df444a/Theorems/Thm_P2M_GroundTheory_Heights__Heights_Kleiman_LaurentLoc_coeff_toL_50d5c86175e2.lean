-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_coeff_toL_50d5c86175e2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_coeff_toL_50d5c86175e2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:01.827708+00:00
-- url     : https://prove2.me/theorems/30a145ed-4f23-4ef1-9f1d-9f157b2d168a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc coeff to L 50d5c86175e2: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc coeff to L 50d5c86175e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc coeff to L 50d5c86175e2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc coeff to L 50d5c86175e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L32-L32

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_coeff_toL_50d5c86175e2 (p : Poly S N) : (toL S N p).coeff = polyToLaurent S N p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«coeff_toL» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_coeff_toL_50d5c86175e2
