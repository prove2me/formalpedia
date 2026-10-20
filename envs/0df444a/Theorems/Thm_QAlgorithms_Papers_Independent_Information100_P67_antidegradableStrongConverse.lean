-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_antidegradableStrongConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P67.antidegradableStrongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:02:13.729974+00:00
-- url     : https://prove2.me/theorems/b955d6fb-e3bf-412d-98e7-df24f204cb5f
-- title:
--   Corollary 7.2 (Antidegradable channels)
-- statement:
--   Let $\mathcal N:A\to B$ be finite-dimensional and antidegradable, with one fixed Stinespring complement. For every rate $R>0$ there are $\gamma>0$ and $n_0\ge1$, depending only on the channel and $R$, such that every valid unassisted $(n,M)$ code with $n\ge n_0$ and $\log_2M\ge nR$ satisfies
--
--   $$f(\mathcal C_n)\le2^{-\gamma n},\qquad \varepsilon_{\max}(\mathcal C_n),\ \varepsilon_{\rm marg}(\mathcal C_n)\ge1-2^{-\gamma n}.$$
--
--   The uniform optimized error is $1-f$, and all three operational private capacities are zero. Antidegradability means that the receiver channel is obtained by processing the complement. No pure symmetric extension is required.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 33, Corollary 7.2 (Antidegradable channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Corollary 7.2, PDF pp.33–34: mixed symmetric extensions are allowed;
no symmetric-pure-range hypothesis is imposed on antidegradable channels. -/
theorem antidegradableStrongConverse [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsAntidegradable U) :
    (∀ rate : ℝ, 0 < rate → ∃ gamma : ℝ, 0 < gamma ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n ≥ n0, ∀ code : PrivateCode A B n, code.Valid →
        (n : ℝ) * rate ≤ Real.logb 2 code.M →
        optimizedFidelity U code ≤ Real.rpow 2 (-gamma * n) ∧
        1 - Real.rpow 2 (-gamma * n) ≤ maximalError U code ∧
        1 - Real.rpow 2 (-gamma * n) ≤ marginalError U code) ∧
    (∀ criterion, privateCapacity criterion U = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
