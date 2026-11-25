-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_mem_78c06350742c
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_mem_78c06350742c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:13.652862+00:00
-- url     : https://prove2.me/theorems/fc1971e1-a1a4-5647-9bde-efb28620d597
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Pt mem 78c06350742c: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Pt mem 78c06350742c
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Pt mem 78c06350742c construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Pt mem 78c06350742c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L92-L96

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

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_mem_78c06350742c {P : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin d → MvPolynomial (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ zeroSet P) : graphPt p x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«graphPt_mem» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_mem_78c06350742c
