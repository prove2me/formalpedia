-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_linForm_ne_zero_922cf3447b3b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_linForm_ne_zero_922cf3447b3b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:25:19.827727+00:00
-- url     : https://prove2.me/theorems/f8d60494-a998-4aff-ba31-dfdeb51790cf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout lin Form ne zero 922cf3447b3b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout lin Form
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout lin Form ne zero 922cf3447b3b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout lin Form ne zero 922cf3447b3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L274-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L274-L276

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_linForm_ne_zero_922cf3447b3b : linForm (![1, 0] : Fin 2 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 2))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ArithBezout».«linForm_ne_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_linForm_ne_zero_922cf3447b3b
