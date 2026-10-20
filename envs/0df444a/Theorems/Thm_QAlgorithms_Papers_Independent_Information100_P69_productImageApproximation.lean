-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_productImageApproximation
-- name    : QAlgorithms.Papers.Independent.Information100.P69.productImageApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:10:37.113258+00:00
-- url     : https://prove2.me/theorems/ece85f84-f0c8-469e-bf3f-e8556f988990
-- title:
--   Approximation of a product-image projector
-- statement:
--   On a local space $A\otimes C_0$, fix a unit vector $|0\rangle\in C_0$ and put $P_k=I_{A^k}\otimes(|0\rangle\langle0|)^{\otimes k}$, using paired-site ordering. For $k\ge2$ and $0<\xi\le1/16$, set $\ell=\lceil\sqrt{k}\ln(2/\xi)\rceil$. There is an operator $H_{k,\xi}$ with a finite supported-contraction expansion satisfying
--   $$\|H_{k,\xi}\|_\infty\le1,\quad\|H_{k,\xi}-P_k\|_\infty\le\xi,\quad |S_i|\le\min\{k,\ell\},\quad\sum_i|c_i|\le15^\ell.$$
--   This is an existence statement for the approximation and its expansion, including a one-dimensional $C_0$. It controls the free-domination cost of a product-image correction.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 33, Lemma 29

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 29, paired-site product-image projection, sqrt(k) times log, and exponential
coefficient cost 15^ell; PDF p.33. -/
theorem productImageApproximation [Nonempty A] {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (zero : EuclideanSpace ℂ C) (hzero : ‖zero‖ = 1) (k : ℕ) (hk : 2 ≤ k)
    (xi : ℝ) (hxi : 0 < xi) (hxi16 : xi ≤ 1/16) :
    let ell : ℕ := Nat.ceil (Real.sqrt k*Real.log (2/xi))
    ∃ P : LocalExpansion (A × C) k, specNorm P.operator ≤ 1 ∧
      specNorm (P.operator-imageProjector (A := A) zero k) ≤ xi ∧
      (∀ i, (P.support i).card ≤ min k ell) ∧ P.cost ≤ (15:ℝ)^ell := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
