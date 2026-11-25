-- Prove2me | Theorems.Thm_P2M_PI_OneCosetSharp_W_Nums_n__ge_f7fc7b2f5918
-- name    : P2M_PI_OneCosetSharp_W_Nums_n__ge_f7fc7b2f5918
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:56.771941+00:00
-- url     : https://prove2.me/theorems/3c38e5c5-8715-5b25-aaf8-74f532b641fd
-- title:
--   P2 M PI One Coset Sharp W Nums n  ge f7fc7b2f5918: P2 M PI One Coset Sharp W Nums n  ge f7fc7b2f5918
-- statement:
--   The P2 M PI One Coset Sharp W Nums n  ge f7fc7b2f5918 construction uses the P2 M PI One Coset Sharp W Nums n  ge f7fc7b2f5918 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/Assemble.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/Assemble.lean#L50-L53

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE

theorem P2M_PI_OneCosetSharp_W_Nums_n__ge_f7fc7b2f5918 {k₀ m t j n' c n : ℕ} (hn : Nums k₀ m t j n' c n) : k₀ ≤ n' := by sorry

alias «PI».«OneCosetSharp».«W».«Nums».«n'_ge» := P2M_PI_OneCosetSharp_W_Nums_n__ge_f7fc7b2f5918
