-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_averageOfProjections
-- name    : QAlgorithms.Papers.Independent.Information100.P67.averageOfProjections
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:54:14.440124+00:00
-- url     : https://prove2.me/theorems/37b821f6-af9c-4b29-87e8-696d75175b14
-- title:
--   Lemma 4.2 (Average of projections)
-- statement:
--   Let $n\ge0$ and let $P_x$ be self-adjoint idempotent matrices on a common nonzero finite-dimensional Hilbert space, indexed by $x\in\{0,1\}^n$. Set $A=2^{-n}\sum_xP_x$ and $U_0[x,y]=2^{-n}$. Let $W$ be real symmetric, and let $\zeta,\ell,\eta\ge0$ satisfy $\|W-U_0\|_{\rm op}\le\zeta$, $\sum_y|W_{xy}|\le\ell$ for every $x$, and $\|P_xP_y\|_{\rm op}\le\eta$ whenever $W_{xy}\ne0$. Then
--
--   $$\|A\|_{\rm op}\le\zeta+\sqrt{\ell\eta}.$$
--
--   No commutativity, mutually orthogonal ranges, or row-sum-one condition is required. The estimate includes zero projections and the singleton label space at $n=0$.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 21, Lemma 4.2 (Average of projections)

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

/-- Lemma 4.2, PDF pp.21–22 (cf. [KBK+26, Lemma S1]).
Each P is self-adjoint idempotent; different P need not commute. -/
theorem averageOfProjections {n : ℕ} [Nonempty A]
    (P : (Fin n → Bool) → Matrix A A ℂ)
    (hP : ∀ x, (P x)ᴴ = P x ∧ P x * P x = P x)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (hW : W.transpose = W)
    (zeta ell eta : ℝ) (hz : 0 ≤ zeta) (hl : 0 ≤ ell) (he : 0 ≤ eta)
    (happrox : specNorm (W - uniformLabelMatrix n) ≤ zeta)
    (hrow : ∀ x, ∑ y, |W x y| ≤ ell)
    (hoverlap : ∀ x y, W x y ≠ 0 → specNorm (P x * P y) ≤ eta) :
    specNorm (((((2 : ℝ) ^ n)⁻¹ : ℂ)) • ∑ x, P x) ≤ zeta + Real.sqrt (ell * eta) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
