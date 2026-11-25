-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_C2_prod_blocks
-- name    : PI.OneCosetSharp.W.C2.prod_blocks
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:15:35.657711+00:00
-- url     : https://prove2.me/theorems/b42dc275-cb23-4e95-a210-b221816c4b38
-- title:
--   C2: prod blocks
-- statement:
--   The C2 construction uses the prod blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L130-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L130-L154

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
open Classical

theorem PI.OneCosetSharp.W.C2.prod_blocks {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k) :
    ∏ i ∈ Finset.range (j - 1), chiV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
      ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) (k₀ + m - 1 + i * t + s.1) (k₀ + m - 1 + i * t + s'.1))) = 1 := by sorry
