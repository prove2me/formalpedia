-- Prove2me | Theorems.Thm_Plasticity_CUB35
-- name    : Plasticity.CUB35
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T08:54:22.657649+00:00
-- url     : https://prove2.me/theorems/f6f50e06-e952-4c11-b902-d41fb8f33d00
-- title:
--   The unit ball of $c_{00}(\Gamma)$ is plastic
-- statement:
--   For every set $\Gamma$, every nonexpansive bijection of the closed unit ball of $c_{00}(\Gamma)$ (finitely supported real functions on $\Gamma$, supremum norm) onto itself is an isometry.
-- source:
--   This repository: claim CUB35 (claims/cub.md, for Γ = ℕ) and expositions/c0_between_spaces.md, Corollary 4 (iii), for every Γ

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_SeqSpace

namespace Plasticity
theorem CUB35 (Γ : Type*) : HasPlasticUnitBall (c00 Γ) := by sorry
end Plasticity
