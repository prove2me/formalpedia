-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finitePlace_aeval_le_one_12b3c7fec63e
-- name    : P2M_GroundTheory_Heights__Heights_finitePlace_aeval_le_one_12b3c7fec63e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:48.325042+00:00
-- url     : https://prove2.me/theorems/707aea46-4fc3-4d73-8931-37234e569015
-- title:
--   P2 M Ground Theory Heights  Heights finite Place aeval le one 12b3c7fec63e: P2 M Ground Theory Heights  Heights finite Place aeval le one 12b3c7fec63e
-- statement:
--   The P2 M Ground Theory Heights  Heights finite Place aeval le one 12b3c7fec63e construction uses the P2 M Ground Theory Heights  Heights finite Place aeval le one 12b3c7fec63e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L82-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L82-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_finitePlace_aeval_le_one_12b3c7fec63e {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {σ : Type*} (y : σ → K) (hy : ∀ p, v (y p) ≤ 1) (g : MvPolynomial σ ℤ) :
    v (aeval y g) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finitePlace_aeval_le_one» := P2M_GroundTheory_Heights__Heights_finitePlace_aeval_le_one_12b3c7fec63e
