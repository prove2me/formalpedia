-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_C2_term_eq
-- name    : PI.OneCosetSharp.W.C2.term_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:15:50.330572+00:00
-- url     : https://prove2.me/theorems/ee051946-dbe7-4246-8e56-ed9bcfcd7fb0
-- title:
--   C2: term eq
-- statement:
--   The C2 construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L191-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L191-L204

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

theorem PI.OneCosetSharp.W.C2.term_eq {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k) :
    PhiS ψ₀ χ k₀ m t j n' c n (xx1 (xj0 k₀ n' n) τ) *
        ψ₀ (-chArg (n' := n') (c' := c + 1) (n := n) (c := c) (xx1 (xj0 k₀ n' n) τ)) =
      if ((∀ p', p' < k₀ + m - 1 → ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p' p' = 1) ∧
        (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' →
          ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' ≠ 0 → Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p'))
      then 1 else 0 := by sorry
