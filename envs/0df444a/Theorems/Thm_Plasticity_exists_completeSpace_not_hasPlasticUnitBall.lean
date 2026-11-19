-- Prove2me | Theorems.Thm_Plasticity_exists_completeSpace_not_hasPlasticUnitBall
-- name    : Plasticity.exists_completeSpace_not_hasPlasticUnitBall
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T19:26:09.112719+00:00
-- url     : https://prove2.me/theorems/e38c5f8a-cf7e-4fe6-b7f5-2183efdfd73f
-- title:
--   Some real Banach space has a nonplastic closed unit ball
-- statement:
--   There is a real Banach space $Z$ whose closed unit ball $B_Z$ is not plastic: some nonexpansive bijection $B_Z\to B_Z$ is not an isometry.
--   This answers negatively the question of Cascales, Kadets, Orihuela and Wingler (2016) whether the unit ball of every Banach space is plastic.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Construction A with Lemma 2.2; question: Cascales, Kadets, Orihuela, Wingler, RACSAM 110 (2016)

import Definitions.Def_Plasticity_Basic

namespace Plasticity
theorem exists_completeSpace_not_hasPlasticUnitBall :
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
      CompleteSpace Z ∧ ¬ HasPlasticUnitBall Z := by sorry
end Plasticity
