-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isChowForm_point_e29c8ba3cc02
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isChowForm_point_e29c8ba3cc02
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:07.856566+00:00
-- url     : https://prove2.me/theorems/0d61cbf2-db46-4bf1-9be3-74fec6457642
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout is Chow Form point e29c8ba3cc02: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout is Chow
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout is Chow Form point e29c8ba3cc02 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout is Chow Form point e29c8ba3cc02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L386-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L386-L411

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isChowForm_point_e29c8ba3cc02 :
    IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 1)))) 0 1
      (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ArithBezout».«isChowForm_point» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isChowForm_point_e29c8ba3cc02
