-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Capelli_cross_term__f82fd11a3764
-- name    : P2M_GlobalTheory_Capelli_cross_term__f82fd11a3764
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:27.117845+00:00
-- url     : https://prove2.me/theorems/e12328a2-594e-4989-8cf6-f5777f17ac2e
-- title:
--   P2 M Global Theory Capelli cross term  f82fd11a3764: P2 M Global Theory Capelli cross term  f82fd11a3764
-- statement:
--   The P2 M Global Theory Capelli cross term  f82fd11a3764 construction uses the P2 M Global Theory Capelli cross term  f82fd11a3764 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L194-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L194-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]

theorem P2M_GlobalTheory_Capelli_cross_term__f82fd11a3764 {K σ : Type*} [CommRing K] {p q n : ℕ} (z : Fin p × Fin n → σ)
    (y : Fin q × Fin n → σ) (hzy : ∀ u w, z u ≠ y w) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ b, X (y (b, k)) * pderiv (y (b, l))
        (∑ a, X (z (a, k)) * pderiv (z (a, l)) P)) =
      ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by sorry

alias «GlobalTheory».«Capelli».«cross_term'» := P2M_GlobalTheory_Capelli_cross_term__f82fd11a3764
