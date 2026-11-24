-- Prove2me | Theorems.Thm_PI_KoszulExact_uniq
-- name    : PI.KoszulExact.uniq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:18.006773+00:00
-- url     : https://prove2.me/theorems/fc9eb8eb-f9ec-406d-b73d-303cf4edf3bf
-- title:
--   Koszul Exact: uniq
-- statement:
--   The Koszul Exact construction uses the uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ProjKillsLiPow.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/ProjKillsLiPow.lean#L26-L34

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

theorem PI.KoszulExact.uniq (i : Fin D) (p q : ℕ) (u v : ExteriorAlgebra R (Fin D → R))
    (hu : u ∈ Li R D i ^ p) (hv : v ∈ Li R D i ^ q) (h : u + eb R i * v = 0) : v = 0 ∧ u = 0 := by sorry
