-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_map_baf010c3c500
-- name    : P2M_GroundTheory_Heights__Heights_isHomogIdeal_map_baf010c3c500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:32.882694+00:00
-- url     : https://prove2.me/theorems/db403d5c-c05a-4b78-925d-cb60e163307a
-- title:
--   P2 M Ground Theory Heights  Heights is Homog Ideal map baf010c3c500: P2 M Ground Theory Heights  Heights is Homog Ideal map baf010c3c500
-- statement:
--   The P2 M Ground Theory Heights  Heights is Homog Ideal map baf010c3c500 construction uses the P2 M Ground Theory Heights  Heights is Homog Ideal map baf010c3c500 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormBaseChange.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormBaseChange.lean#L13-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormBaseChange
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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_isHomogIdeal_map_baf010c3c500 {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S)
    {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I) :
    IsHomogIdeal (I.map (MvPolynomial.map φ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isHomogIdeal_map» := P2M_GroundTheory_Heights__Heights_isHomogIdeal_map_baf010c3c500
