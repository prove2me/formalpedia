-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_neg_log_monoNormSq_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_monoNormSq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:57.489934+00:00
-- url     : https://prove2.me/theorems/8afc34bd-01eb-42eb-95fd-d13240d7b69c
-- title:
--   Geometry Of Numbers Theory: chi PAux neg log mono Norm Sq le
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux neg log mono Norm Sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L253-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L253-L273

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_monoNormSq_le {D : ℕ} (b : Fin (D + 1) → ℕ) :
    -Real.log (monoNormSq b) ≤
      (∑ i, b i : ℕ) * Real.log (D + 1) + D * Real.log ((∑ i, b i : ℕ) + D) := by sorry
