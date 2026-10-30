-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_symmetricSideAssistance
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.symmetricSideAssistance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:53:52.108051+00:00
-- url     : https://prove2.me/theorems/d06b847c-579b-4621-99f1-6b433984e287
-- title:
--   Section IX: unbounded rates with a free symmetric side channel
-- statement:
--   Let $\mathcal N$ be any quantum channel on nonzero finite systems and fix an integer $n\ge1$. Permit one free symmetric side channel of arbitrary finite input dimension. For every integer $m\ge1$, the 50%-50% erasure channel on $\mathbb C^m$, with a flag orthogonal to all input states, is degradable and antidegradable. Feed half of the normalized maximally entangled state $\Phi_m$ through that side channel, feed a fixed pure state to the $n$ uses of $\mathcal N$, discard the latter output, and decode the erasure flag to a fixed basis state. This is a valid entanglement-generating code of rank $m$, with
--
--   $$
--   F^2=\frac{1+m^{-2}}2,\qquad P=\sqrt{\frac{1-m^{-2}}2}\le\frac1{\sqrt2}.
--   $$
--
--   Moreover, for every real rate $R$ there exists a finite $m$ for which this code has $\log_2 m/n\ge R$. Thus finite-block rates are unbounded at this fixed assisted error. No infinite-dimensional code or unassisted capacity assertion is used.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 13, Section IX: unbounded rates with a free symmetric side channel

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Section IX symmetric-side assistance Remark, PDF p.13: one free
50%-50% erasure side channel, of arbitrary finite dimension, suffices.
The actual unassisted n-use channel is still present in parallel and may be ignored.
The exact squared fidelity is (1+1/m^2)/2. -/
theorem symmetricSideAssistance [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : P67.IsIsometry U) (n : ℕ) (hn : 1 ≤ n) :
    (∀ m : ℕ, ∀ hm : 0 < m,
      P67.IsDegradable (P67.erasureDilation (A := Fin m) (1 / 2)) ∧
      P67.IsAntidegradable (P67.erasureDilation (A := Fin m) (1 / 2)) ∧
      let code := erasureSideCode (A := A) (B := B) n m hm
      code.Valid ∧ code.dimension = m ∧
      code.error (idTensorSuperop (halfErasure m) ∘ P67.mapFirst (P67.receiverChannel (P67.dilationPower U n))) =
        Real.sqrt ((1 - 1 / (m : ℝ) ^ 2) / 2) ∧
      code.error (idTensorSuperop (halfErasure m) ∘ P67.mapFirst (P67.receiverChannel (P67.dilationPower U n))) ≤ 1 / Real.sqrt 2) ∧
    (∀ rate : ℝ, ∃ m : ℕ, ∃ hm : 0 < m,
      let code := erasureSideCode (A := A) (B := B) n m hm
      code.Valid ∧ (n : ℝ) * rate ≤ Real.logb 2 m ∧
      code.error (idTensorSuperop (halfErasure m) ∘ P67.mapFirst (P67.receiverChannel (P67.dilationPower U n))) ≤ 1 / Real.sqrt 2) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
