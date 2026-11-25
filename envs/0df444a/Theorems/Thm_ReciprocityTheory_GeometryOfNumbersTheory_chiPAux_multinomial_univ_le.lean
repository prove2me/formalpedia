-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_multinomial_univ_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_multinomial_univ_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:38.253145+00:00
-- url     : https://prove2.me/theorems/fb676350-d8e7-4dcc-b20d-42c9b279c951
-- title:
--   Geometry Of Numbers Theory: chi PAux multinomial univ le
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux multinomial univ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L35-L43

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_multinomial_univ_le {D : ℕ} (a : Fin (D + 1) → ℕ) :
    Nat.multinomial Finset.univ a ≤ (D + 1) ^ (∑ i, a i) := by sorry
