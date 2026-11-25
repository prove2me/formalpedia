-- Prove2me | Theorems.Thm_PI_KoszulExact_eb_mem_Li
-- name    : PI.KoszulExact.eb_mem_Li
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:33:53.126982+00:00
-- url     : https://prove2.me/theorems/b70849d8-9f8e-4e52-820a-4401a2247aa5
-- title:
--   Koszul Exact: eb mem Li
-- statement:
--   The Koszul Exact construction uses the eb mem Li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/Decomp.lean#L39-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp
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

theorem PI.KoszulExact.eb_mem_Li (k : Fin D) (i : ℕ) (hk : (k : ℕ) < i) : eb R k ∈ Li R D i := by sorry
