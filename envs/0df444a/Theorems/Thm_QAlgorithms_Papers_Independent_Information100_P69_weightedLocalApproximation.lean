-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_weightedLocalApproximation
-- name    : QAlgorithms.Papers.Independent.Information100.P69.weightedLocalApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:09:09.065101+00:00
-- url     : https://prove2.me/theorems/c80bbe54-384a-477a-8a51-a3323b57d9d4
-- title:
--   Weighted discarding and local approximation
-- statement:
--   Fix local dimension $d\ge1$ and $t>0$. There are $n_0$ and $C_{d,t}\ge0$, uniform over faithful states $\tau$ with minimum eigenvalue $t$, such that for $n\ge n_0$, $0<\xi\le1/16$, and
--   $$m=\lceil n^{2/3}\ln((n+1)/\xi)\rceil,\quad k+m=n,\quad m\le n/2,$$
--   every permutation-invariant contraction $W$ has a finite supported-contraction expansion $P=\sum_i c_iF_i$ with
--   $$\|P-\mathcal E_{\tau,m}(W)\|_\infty\le\xi,\quad|S_i|\le C_{d,t}n^{2/3},\quad\sum_i|c_i|\le e^{C_{d,t}n^{2/3}}.$$
--   Here $F_i$ is supported on its chosen site subset $S_i$ and $\mathcal E_{\tau,m}(W)$ is the partial trace of $(I\otimes(\tau^{1/2})^{\otimes m})W(I\otimes(\tau^{1/2})^{\otimes m})$. This weighted-discarding map is unital and CP. The constants are uniform in $\xi,W$, and empty supports cover $d=1$.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 30, Lemma 27

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 27, weighted discarding and a finite local contraction expansion; active-regime
hypothesis is retained; constants uniform in the state eigenbasis, xi, and W; PDF pp.30–31. -/
theorem weightedLocalApproximation [Nonempty A] (t : ℝ) (ht : 0 < t) :
    ∃ n0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ tau : Matrix A A ℂ,
      Faithful tau → minPositiveEigenvalue tau = t →
      ∀ n, 1 ≤ n → n0 ≤ n → ∀ xi : ℝ, 0 < xi → xi ≤ 1/16 →
      let m : ℕ := Nat.ceil ((n:ℝ)^(2/3:ℝ)*Real.log (((n:ℝ)+1)/xi))
      ∀ k : ℕ, ∀ hkm : k+m=n, 2*m ≤ n →
      (CP (weightedDiscard hkm tau) ∧ weightedDiscard hkm tau 1 = 1) ∧
      ∀ W : Matrix (Sites A n) (Sites A n) ℂ,
        (∀ pi, permute pi W = W) → specNorm W ≤ 1 →
        ∃ P : LocalExpansion A k,
          specNorm (P.operator-weightedDiscard hkm tau W) ≤ xi ∧
          (∀ i, ((P.support i).card:ℝ) ≤ C*(n:ℝ)^(2/3:ℝ)) ∧
          P.cost ≤ Real.exp (C*(n:ℝ)^(2/3:ℝ)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
