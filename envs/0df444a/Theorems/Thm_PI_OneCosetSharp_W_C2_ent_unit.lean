-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_C2_ent_unit
-- name    : PI.OneCosetSharp.W.C2.ent_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:46.240635+00:00
-- url     : https://prove2.me/theorems/e252f16c-47a5-44d8-b362-6277b3575fc4
-- title:
--   C2: ent unit
-- statement:
--   The C2 construction uses the ent unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L65-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L65-L77

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

theorem PI.OneCosetSharp.W.C2.ent_unit {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (τ : FC n' (c + 1) n c → k) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n' + (c + 1)) (hcol : p' ≤ k₀ ∨ k₀ + c < p') :
    ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' = if p = p' then 1 else 0 := by sorry
