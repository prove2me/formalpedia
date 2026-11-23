-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_C2_facts
-- name    : PI.OneCosetSharp.W.C2.facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:36.640528+00:00
-- url     : https://prove2.me/theorems/a99a46a4-ffcc-4783-aa25-843469a04060
-- title:
--   C2: facts
-- statement:
--   The C2 construction uses the facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L46-L53

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

theorem PI.OneCosetSharp.W.C2.facts {k₀ m t j n' c n : ℕ} (h : Nums k₀ m t j n' c n) :
    k₀ ≤ n' ∧ 1 ≤ c ∧ k₀ + c < k₀ + m - 1 ∧ k₀ + m - 1 ≤ n' + (c + 1) ∧ n' + (c + 1) ≤ n + c ∧
      n' + (c + 1) = k₀ + m - 1 + (j - 1) * t ∧ n + c = n' + (c + 1) + t := by sorry
