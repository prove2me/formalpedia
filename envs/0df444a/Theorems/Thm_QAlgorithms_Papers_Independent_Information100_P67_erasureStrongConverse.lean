-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_erasureStrongConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P67.erasureStrongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:02:52.279446+00:00
-- url     : https://prove2.me/theorems/3008d5db-03a4-467d-bd81-42d3e7255b75
-- title:
--   Corollary 7.3 (All erasure probabilities)
-- statement:
--   For every positive input dimension $d_0$ and every $p\in[0,1]$, consider the orthogonal-flag erasure channel $\mathcal E_{p,d_0}(X)=(1-p)X\oplus p\operatorname{Tr}(X)|e\rangle\langle e|$, with an erasure flag orthogonal to the input space. Its explicitly specified dilation sends $|a\rangle$ to $\sqrt{1-p}|a,e\rangle+\sqrt p|e,a\rangle$. Under each of the uniform optimized, maximal optimized, and actual-marginal joint criteria,
--
--   $$P(\mathcal E_{p,d_0})=[1-2p]_+\log_2d_0.$$
--
--   For every gap $\Delta>0$ above this threshold there exist code-independent $\gamma>0,n_0\ge1$ such that all valid $(n,M)$ codes with $n\ge n_0$ and $\log_2M\ge n(P+\Delta)$ satisfy $f\le2^{-\gamma n}$ and maximal/actual-marginal infidelity at least $1-2^{-\gamma n}$. This includes $p=0,1/2,1$ and $d_0=1$.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 34, Corollary 7.3 (All erasure probabilities)

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

/-- Corollary 7.3, PDF p.34: every erasure probability, including endpoints,
and arbitrary positive input dimension (including one). -/
theorem erasureStrongConverse [Nonempty A] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let U := erasureDilation (A := A) p
    let q := max (1 - 2 * p) 0 * Real.logb 2 (Fintype.card A)
    IsIsometry U ∧ (∀ criterion, privateCapacity criterion U = q) ∧
    (∀ gap : ℝ, 0 < gap → ∃ gamma : ℝ, 0 < gamma ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n ≥ n0, ∀ code : PrivateCode A (Option A) n, code.Valid →
        (n : ℝ) * (q + gap) ≤ Real.logb 2 code.M →
        optimizedFidelity U code ≤ Real.rpow 2 (-gamma * n) ∧
        1 - Real.rpow 2 (-gamma * n) ≤ maximalError U code ∧
        1 - Real.rpow 2 (-gamma * n) ≤ marginalError U code) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
