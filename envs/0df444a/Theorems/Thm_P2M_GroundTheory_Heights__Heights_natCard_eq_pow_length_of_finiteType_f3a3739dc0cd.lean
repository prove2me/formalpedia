-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_natCard_eq_pow_length_of_finiteType_f3a3739dc0cd
-- name    : P2M_GroundTheory_Heights__Heights_natCard_eq_pow_length_of_finiteType_f3a3739dc0cd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:32.631811+00:00
-- url     : https://prove2.me/theorems/53910414-0ea1-49f8-993c-da24d64416e9
-- title:
--   P2 M Ground Theory Heights  Heights nat Card eq pow length of finite Type f3a3739dc0cd: P2 M Ground Theory Heights  Heights nat Card eq pow length of finite Type f3a3739dc0cd
-- statement:
--   The P2 M Ground Theory Heights  Heights nat Card eq pow length of finite Type f3a3739dc0cd construction uses the P2 M Ground Theory Heights  Heights nat Card eq pow length of finite Type f3a3739dc0cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartResidue.lean#L25-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartResidue.lean#L25-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartDehom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartResidue
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

theorem P2M_GroundTheory_Heights__Heights_natCard_eq_pow_length_of_finiteType_f3a3739dc0cd (F : Type) [Field F] [Algebra.FiniteType ℤ F]
    (q : ℕ) [CharP F q] :
    q.Prime ∧ Nat.card F = q ^ (Module.length ℤ F).toNat := by sorry

alias «GroundTheory».«Heights₂».«Heights».«natCard_eq_pow_length_of_finiteType» := P2M_GroundTheory_Heights__Heights_natCard_eq_pow_length_of_finiteType_f3a3739dc0cd
