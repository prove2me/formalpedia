-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_eval_linPoly_2c3dac8bdfd6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_eval_linPoly_2c3dac8bdfd6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:03.377022+00:00
-- url     : https://prove2.me/theorems/09783e15-c16f-511d-a6ba-8722f29c137f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Isolated Fibre Open Of Generic eval lin Poly 2c3dac8bdfd6: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Isolated Fibre Open Of Generic eval lin Poly 2c3dac8bdfd6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Isolated Fibre Open Of Generic eval lin Poly 2c3dac8bdfd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenFixed.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenFixed.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology Matrix Metric
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_eval_linPoly_2c3dac8bdfd6 {n k : ℕ} (B : Matrix (Fin k) (Fin n) ℂ) (z : Fin n → ℂ) (i : Fin k) :
    eval z (linPoly B.mulVecLin i) = (B *ᵥ z) i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«IsolatedFibreOpenOfGeneric».«eval_linPoly» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_eval_linPoly_2c3dac8bdfd6
