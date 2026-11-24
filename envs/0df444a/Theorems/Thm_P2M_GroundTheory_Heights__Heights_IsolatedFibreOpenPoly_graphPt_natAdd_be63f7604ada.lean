-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_natAdd_be63f7604ada
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_natAdd_be63f7604ada
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:46.30804+00:00
-- url     : https://prove2.me/theorems/acdf2e81-0a8d-4ef6-87b0-60bfcece1eeb
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Pt nat Add be63f7604ada: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Pt nat Add be63f7604ada
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Pt nat Add be63f7604ada construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Pt nat Add be63f7604ada property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L42-L44

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

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_natAdd_be63f7604ada (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (i : Fin d) :
    graphPt p x (Fin.natAdd n i) = eval x (p i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«graphPt_natAdd» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_natAdd_be63f7604ada
