-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionNorm_chartMonomial_ne_zero_33456487209d
-- name    : P2M_GroundTheory_Heights__Heights_SectionNorm_chartMonomial_ne_zero_33456487209d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:38:30.197653+00:00
-- url     : https://prove2.me/theorems/652d9b5c-c278-5ba3-9e8b-fb2703092f3d
-- title:
--   P2 M Ground Theory Heights  Heights Section Norm chart Monomial ne zero 33456487209d: P2 M Ground Theory Heights  Heights Section Norm chart Monomial ne zero 33456487209d
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Norm chart Monomial ne zero 33456487209d construction uses the P2 M Ground Theory Heights  Heights Section Norm chart Monomial ne zero 33456487209d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomial.lean#L26-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomial.lean#L26-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomial
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionNorm

theorem P2M_GroundTheory_Heights__Heights_SectionNorm_chartMonomial_ne_zero_33456487209d {P : ArithVariety n} (D : AddBlockData P) {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (D.size + 1)) (hgz : evalCone z (g c j) ≠ 0) :
    evalCone z (chartMonomial c d) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionNorm».«chartMonomial_ne_zero» := P2M_GroundTheory_Heights__Heights_SectionNorm_chartMonomial_ne_zero_33456487209d
