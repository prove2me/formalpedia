-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_neg_log_monoNormSq_nonneg
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_monoNormSq_nonneg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:52.545308+00:00
-- url     : https://prove2.me/theorems/db15f532-253f-4835-8650-1315a42a1103
-- title:
--   Geometry Of Numbers Theory: chi PAux neg log mono Norm Sq nonneg
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux neg log mono Norm Sq nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L275-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L275-L277

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_monoNormSq_nonneg {D : ℕ} (b : Fin (D + 1) → ℕ) : 0 ≤ -Real.log (monoNormSq b) := by sorry
