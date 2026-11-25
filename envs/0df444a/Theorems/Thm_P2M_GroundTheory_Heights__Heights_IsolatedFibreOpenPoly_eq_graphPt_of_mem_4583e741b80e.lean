-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eq_graphPt_of_mem_4583e741b80e
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eq_graphPt_of_mem_4583e741b80e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:36.899823+00:00
-- url     : https://prove2.me/theorems/4dce44d9-ffa4-43be-a51d-61da3c71acbc
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly eq graph Pt of mem 4583e741b80e: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly eq graph Pt of mem 4583e741b80e
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly eq graph Pt of mem 4583e741b80e construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly eq graph Pt of mem 4583e741b80e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L119-L125

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

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eq_graphPt_of_mem_4583e741b80e {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    z = graphPt p (firstPart z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«eq_graphPt_of_mem» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eq_graphPt_of_mem_4583e741b80e
