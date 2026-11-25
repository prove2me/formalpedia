-- Prove2me | Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_main
-- name    : PositivityTheory.CW.GradedNormalNilpotent.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:30.587949+00:00
-- url     : https://prove2.me/theorems/a31f6f10-47f3-46eb-a3e5-e0e53a139469
-- title:
--   Graded Normal Nilpotent: main
-- statement:
--   The Graded Normal Nilpotent construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L244-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CommutatorAdjointHolds.lean#L244-L294

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.GradedNormalNilpotent
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
variable {ε E}
variable (h : Hyp ε E)
include h

theorem PositivityTheory.CW.GradedNormalNilpotent.main (h2 : ∀ (k : ℕ) c d, E c d * (Mm E ^ k).trace = (Mm E ^ k).trace * E c d)
    (h3 : ∀ T : Module.End ℂ V, (∀ a b, E a b * T = T * E a b) → ∃ c : ℂ, ∀ v, T v = c • v)
    (h4 : A4) (h5 : ∀ a b, (Mm E * Md ε E - Md ε E * Mm E) a b + Z ε E a b ∈ U E 1) :
    ∀ m : ℕ, 1 ≤ m → n ≤ m → ∀ a b, ∃ u ∈ U E (2 * m - 1), ∃ w : Fin n → Fin n → Module.End ℂ V,
      (∀ c d, w c d ∈ U E (2 * m - 2)) ∧ ((Md ε E * Mm E) ^ m) a b = u + ∑ c, ∑ d, w c d * Z ε E c d := by sorry
