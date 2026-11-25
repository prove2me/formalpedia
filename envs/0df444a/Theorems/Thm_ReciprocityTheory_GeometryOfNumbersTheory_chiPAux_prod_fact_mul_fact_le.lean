-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_prod_fact_mul_fact_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_prod_fact_mul_fact_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:46.140692+00:00
-- url     : https://prove2.me/theorems/dc0c6391-b414-4e6f-a5d4-a122cd6a0aea
-- title:
--   Geometry Of Numbers Theory: chi PAux prod fact mul fact le
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux prod fact mul fact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L15-L23

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_prod_fact_mul_fact_le {D : ℕ} (a : Fin (D + 1) → ℕ) :
    (∏ i, (a i).factorial) * D.factorial ≤ ((∑ i, a i) + D).factorial := by sorry
