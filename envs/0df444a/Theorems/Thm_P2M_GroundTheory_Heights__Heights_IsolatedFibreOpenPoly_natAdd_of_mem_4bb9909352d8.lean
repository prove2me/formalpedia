-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_natAdd_of_mem_4bb9909352d8
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_natAdd_of_mem_4bb9909352d8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:30.682247+00:00
-- url     : https://prove2.me/theorems/74767f7e-edc4-4cb6-a2d8-f3bd68ff7b18
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly nat Add of mem 4bb9909352d8: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly nat Add of mem 4bb9909352d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly nat Add of mem 4bb9909352d8 construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly nat Add of mem 4bb9909352d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L109-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
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
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_natAdd_of_mem_4bb9909352d8 {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) (i : Fin d) :
    z (Fin.natAdd n i) = eval (firstPart z) (p i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«natAdd_of_mem» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_natAdd_of_mem_4bb9909352d8
