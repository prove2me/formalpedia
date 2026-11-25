-- Prove2me | Theorems.Thm_P2M_PI_OneCosetSharp_W_C2_ent__0_9e2df1bf3f49
-- name    : P2M_PI_OneCosetSharp_W_C2_ent__0_9e2df1bf3f49
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:02.371145+00:00
-- url     : https://prove2.me/theorems/b03d6265-843f-4a54-9b37-08129838334f
-- title:
--   P2 M PI One Coset Sharp W C2 ent  0 9e2df1bf3f49: P2 M PI One Coset Sharp W C2 ent  0 9e2df1bf3f49
-- statement:
--   The P2 M PI One Coset Sharp W C2 ent  0 9e2df1bf3f49 construction uses the P2 M PI One Coset Sharp W C2 ent  0 9e2df1bf3f49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L79-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L79-L91

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

theorem P2M_PI_OneCosetSharp_W_C2_ent__0_9e2df1bf3f49 {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n' + (c + 1)) :
    ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) (τ0 (k := k) k₀ n' c n)) p p' = if p = p' then 1 else 0 := by sorry

alias «PI».«OneCosetSharp».«W».«C2».«ent_τ0» := P2M_PI_OneCosetSharp_W_C2_ent__0_9e2df1bf3f49
