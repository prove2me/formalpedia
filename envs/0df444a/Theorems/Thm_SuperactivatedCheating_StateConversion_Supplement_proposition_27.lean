-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_Supplement_proposition_27
-- name    : SuperactivatedCheating.StateConversion.Supplement.proposition_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:07.141058+00:00
-- url     : https://prove2.me/theorems/05e8ca1b-ce37-4325-b9f1-b84e8295c956
-- title:
--   Proposition 27 (used in the proof of Theorem 28) — OTP direct-sum capacities
-- statement:
--   Let $E_0:\mathcal B(H_0)\to\mathcal B(K)$ and $E_1:\mathcal B(H_1)\to\mathcal B(K)$ be CPTP channels on finite nonzero registers. Let $(U_j)_{j\in J}$ be any finite nonempty unitary 1-design on $K$, and let $N=E_0\oplus_{\rm OTP}E_1$ be Definition 25’s keyed direct sum. This map is CPTP and
--   $$C_0^{(1)}(N^{\otimes n})\ge\max_{s\in\{0,1\}^n}C_0^{(1)}(E_{s_1}\otimes\cdots\otimes E_{s_n})\quad(n\ge1),$$
--   $$C_0^{(1)}(N)=\max\{C_0^{(1)}(E_0),C_0^{(1)}(E_1)\}.$$
--   The branches may have different input dimensions. These are classical zero-error capacities. Both the full tensor-word bound and the one-shot equality support Theorem 28.
--
--   Differences from the source:
--   - encoding: maximum over all binary tensor words and nonnegative one-shot capacities → finite indexed supremum in ℝ≥0∞, with validity of the constructed CPTP map also asserted; reason: the word set is finite and nonempty; its supremum is its maximum; distinct input spaces remain allowed
--   - encoding: finite-dimensional registers and CPTP operations → finite types in Type 0 with decidable equality, coordinate matrices and the published finite normalized Kraus channel predicate; reason: every finite register and every finite-dimensional CPTP map has this representation; no dimension or rank bound is imposed
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), Proposition 27, p. 22.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Operations

open scoped ENNReal NNReal Matrix
noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement

/-- Proposition 27, eqs.(5.2),(5.3), p.22: all positive powers, all designs,
different branch input spaces. The capacity maximum is the finite supremum over all words. -/
theorem proposition_27 {A B K J : Type}
    [Fintype A] [Fintype B] [Fintype K] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq K] [DecidableEq J]
    [Nonempty A] [Nonempty B] [Nonempty K] [Nonempty J]
    (E₀ : Map A K) (E₁ : Map B K) (h₀ : QAlgorithms.IsChannel E₀)
    (h₁ : QAlgorithms.IsChannel E₁) (U : J → Op K) (hU : IsOneDesign U) :
    QAlgorithms.IsChannel (otp E₀ E₁ U) ∧
    (∀ n : ℕ, 1 ≤ n →
      (⨆ s : Fin n → Bool, C1 (wordMap E₀ E₁ s)) ≤ C1 (power (otp E₀ E₁ U) n)) ∧
    C1 (otp E₀ E₁ U) = max (C1 E₀) (C1 E₁) := by sorry

end SuperactivatedCheating.StateConversion.Supplement
