-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_sup_span_eq_96e87095134c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_sup_span_eq_96e87095134c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:51.496111+00:00
-- url     : https://prove2.me/theorems/1e5f0d35-e169-5e91-9bd7-12d64ff4d366
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Order mult At sup span eq 96e87095134c: P2 M Ground Theory Heights  Heights Inter Diagonal Order mult At sup span eq 96e87095134c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Order mult At sup span eq 96e87095134c construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Order mult At sup span eq 96e87095134c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L28-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrd.lean#L28-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_sup_span_eq_96e87095134c {P W : Ideal (MRing ι)} [P.IsPrime] (hW : W.IsPrime) (hPW : P ≤ W)
    {g h u v : MRing ι} (hu : u ∉ W) (hv : v ∉ W) (hm : u * g - v * h ∈ P) :
    multAt (P ⊔ Ideal.span {g}) W = multAt (P ⊔ Ideal.span {h}) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOrder».«multAt_sup_span_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multAt_sup_span_eq_96e87095134c
