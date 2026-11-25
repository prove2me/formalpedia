-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_count_cross
-- name    : PositivityTheory.Rg.Cz.count_cross
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:04.986312+00:00
-- url     : https://prove2.me/theorems/79fda4b5-7d4f-42eb-af97-9a225ba19d9b
-- title:
--   Cz: count cross
-- statement:
--   The Cz construction uses the count cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/CountCross.lean#L85-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/CountCross.lean#L85-L102

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountSame
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountCross
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}

theorem PositivityTheory.Rg.Cz.count_cross (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) (R : Q → Q → ℝ) (N : ℝ)
    (hsymm : ∀ p q, R p q = R q p)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then R p q else 0) ≤
      ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then N else 0) := by sorry
