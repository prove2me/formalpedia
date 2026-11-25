-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_mem_38bb86ee4503
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_mem_38bb86ee4503
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:24.448471+00:00
-- url     : https://prove2.me/theorems/91f4d075-1e76-43f7-8abd-a41676ffce8a
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly first Part mem 38bb86ee4503: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly first Part mem 38bb86ee4503
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly first Part mem 38bb86ee4503 construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly first Part mem 38bb86ee4503 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L98-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L98-L107

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

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_mem_38bb86ee4503 {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    firstPart z ∈ zeroSet P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«firstPart_mem» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_mem_38bb86ee4503
