-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_C2_fIdx_lt
-- name    : PI.OneCosetSharp.W.C2.fIdx_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:03.085811+00:00
-- url     : https://prove2.me/theorems/0ee75e04-602d-4750-b0ed-80338ae76071
-- title:
--   C2: f Idx lt
-- statement:
--   The C2 construction uses the f Idx lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L55-L57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]

theorem PI.OneCosetSharp.W.C2.fIdx_lt {k₀ c n p : ℕ} (_hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by sorry
