-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_graphPt_177b1d982e4e
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_graphPt_177b1d982e4e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:22.703863+00:00
-- url     : https://prove2.me/theorems/b95d03cb-ff36-4f26-a5e7-dbfa67cef770
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly first Part graph Pt 177b1d982e4e: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly first Part graph Pt 177b1d982e4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly first Part graph Pt 177b1d982e4e construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly first Part graph Pt 177b1d982e4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L37-L40

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

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_graphPt_177b1d982e4e (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    firstPart (graphPt p x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«firstPart_graphPt» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_firstPart_graphPt_177b1d982e4e
