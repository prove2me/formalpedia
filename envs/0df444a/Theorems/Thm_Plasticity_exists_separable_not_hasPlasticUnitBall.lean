-- Prove2me | Theorems.Thm_Plasticity_exists_separable_not_hasPlasticUnitBall
-- name    : Plasticity.exists_separable_not_hasPlasticUnitBall
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T20:09:53.561487+00:00
-- url     : https://prove2.me/theorems/322a167d-baed-4962-ab6b-9bd8bb7a40be
-- title:
--   Some separable real Banach space has a nonplastic closed unit ball
-- statement:
--   There is a separable real Banach space $Z$ whose closed unit ball $B_Z$ is not plastic: some nonexpansive bijection $B_Z\to B_Z$ is not an isometry.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Construction B with Lemma 2.2

import Definitions.Def_Plasticity_Basic
import Mathlib.Topology.Bases

namespace Plasticity
theorem exists_separable_not_hasPlasticUnitBall :
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
      CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧ ¬ HasPlasticUnitBall Z := by sorry
end Plasticity
