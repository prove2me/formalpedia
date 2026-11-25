-- Prove2me | Theorems.Thm_PI_KoszulExact_proj_kills_Li_pow
-- name    : PI.KoszulExact.proj_kills_Li_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:33:53.989817+00:00
-- url     : https://prove2.me/theorems/3d5ee32e-3932-54b8-a27f-2188a1f7cffa
-- title:
--   Koszul Exact: proj kills Li pow
-- statement:
--   The Koszul Exact construction uses the proj kills Li pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ProjKillsLiPow.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ProjKillsLiPow.lean#L12-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ProjKillsLiPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}

theorem PI.KoszulExact.proj_kills_Li_pow (i : Fin D) (p : ℕ) (x : ExteriorAlgebra R (Fin D → R))
    (hx : x ∈ Li R D i ^ p) :
    CliffordAlgebra.contractLeft (LinearMap.proj i : (Fin D → R) →ₗ[R] R) x = 0 := by sorry
