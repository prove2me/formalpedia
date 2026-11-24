-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_notMem_mul_4d76ee15430d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_notMem_mul_4d76ee15430d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:08.469401+00:00
-- url     : https://prove2.me/theorems/4027ba64-8c3b-47d7-bf24-6820e7442353
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals not Mem mul 4d76ee15430d: P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals not Mem mul 4d76ee15430d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals not Mem mul 4d76ee15430d construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals not Mem mul 4d76ee15430d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L24-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_notMem_mul_4d76ee15430d {I : Ideal (MRing ι)} (hI : I.IsPrime) {a b : MRing ι} (ha : a ∉ I) (hb : b ∉ I) :
    a * b ∉ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocMaxIdeals».«notMem_mul» := P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_notMem_mul_4d76ee15430d
