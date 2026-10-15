-- Prove2me | Theorems.Thm_Plasticity_CUB36
-- name    : Plasticity.CUB36
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T08:54:35.93267+00:00
-- url     : https://prove2.me/theorems/3fdb767b-ff14-4c59-bcc2-1f43ebca669a
-- title:
--   The unit ball of $c_0(\Gamma)$ is plastic
-- statement:
--   For every set $\Gamma$, every nonexpansive bijection of the closed unit ball of $c_0(\Gamma)$ (real functions on $\Gamma$ vanishing at infinity, supremum norm) onto itself is an isometry.
--   No continuity of the inverse is assumed.
-- source:
--   This repository: claim CUB36 (claims/cub.md, for Γ = ℕ) and expositions/c0_between_spaces.md, Corollary 4 (iii), for every Γ

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_SeqSpace

namespace Plasticity
theorem CUB36 (Γ : Type*) : HasPlasticUnitBall (c0 Γ) := by sorry
end Plasticity
