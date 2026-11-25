-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_poly_coeff_zero_ne_zero_3cecf393ad2e
-- name    : P2M_GroundTheory_Heights__Heights_exists_int_poly_coeff_zero_ne_zero_3cecf393ad2e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:23.591154+00:00
-- url     : https://prove2.me/theorems/07ead2bd-1566-46b4-ae20-e560ac0efd0b
-- title:
--   P2 M Ground Theory Heights  Heights exists int poly coeff zero ne zero 3cecf393ad2e: P2 M Ground Theory Heights  Heights exists int poly coeff zero ne zero 3cecf393ad2e
-- statement:
--   The P2 M Ground Theory Heights  Heights exists int poly coeff zero ne zero 3cecf393ad2e construction uses the P2 M Ground Theory Heights  Heights exists int poly coeff zero ne zero 3cecf393ad2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDivVertical.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDivVertical.lean#L10-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDivVertical
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem P2M_GroundTheory_Heights__Heights_exists_int_poly_coeff_zero_ne_zero_3cecf393ad2e {τ : AlgebraicClosure ℚ} (hτ : τ ≠ 0) :
    ∃ P : Polynomial ℤ, P.coeff 0 ≠ 0 ∧ Polynomial.aeval τ P = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_int_poly_coeff_zero_ne_zero» := P2M_GroundTheory_Heights__Heights_exists_int_poly_coeff_zero_ne_zero_3cecf393ad2e
