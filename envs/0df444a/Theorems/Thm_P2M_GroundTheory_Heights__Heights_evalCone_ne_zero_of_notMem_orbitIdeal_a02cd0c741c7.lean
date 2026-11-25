-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_ne_zero_of_notMem_orbitIdeal_a02cd0c741c7
-- name    : P2M_GroundTheory_Heights__Heights_evalCone_ne_zero_of_notMem_orbitIdeal_a02cd0c741c7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:04.645274+00:00
-- url     : https://prove2.me/theorems/bde3922c-4895-467b-b48b-5edce4ef0ebd
-- title:
--   P2 M Ground Theory Heights  Heights eval Cone ne zero of not Mem orbit Ideal a02cd0c741c7: P2 M Ground Theory Heights  Heights eval Cone ne zero of not Mem orbit Ideal a02cd0c741c7
-- statement:
--   The P2 M Ground Theory Heights  Heights eval Cone ne zero of not Mem orbit Ideal a02cd0c741c7 construction uses the P2 M Ground Theory Heights  Heights eval Cone ne zero of not Mem orbit Ideal a02cd0c741c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartTerm.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartTerm.lean#L39-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartTerm
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_evalCone_ne_zero_of_notMem_orbitIdeal_a02cd0c741c7 (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a)
    (hW : s ∉ orbitIdeal x) : evalCone x s ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«evalCone_ne_zero_of_notMem_orbitIdeal» := P2M_GroundTheory_Heights__Heights_evalCone_ne_zero_of_notMem_orbitIdeal_a02cd0c741c7
