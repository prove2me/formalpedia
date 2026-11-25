-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_continuous_firstPart_81c0042172c5
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_continuous_firstPart_81c0042172c5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:12.76216+00:00
-- url     : https://prove2.me/theorems/8b49c00d-ca60-45ee-b0d2-228bbac6dfd8
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly continuous first Part 81c0042172c5: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly continuous first Part 81c0042172c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly continuous first Part 81c0042172c5 construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly continuous first Part 81c0042172c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L46-L47

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

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_continuous_firstPart_81c0042172c5 : Continuous (firstPart : (Fin (n + d) → ℂ) → Fin n → ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«continuous_firstPart» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_continuous_firstPart_81c0042172c5
