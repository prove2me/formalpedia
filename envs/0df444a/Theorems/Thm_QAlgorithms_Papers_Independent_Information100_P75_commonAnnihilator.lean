-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_commonAnnihilator
-- name    : QAlgorithms.Papers.Independent.Information100.P75.commonAnnihilator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:14:27.619465+00:00
-- url     : https://prove2.me/theorems/d466d95f-b7db-45c6-a5c3-f965dd6676e1
-- title:
--   Pointwise relaxed annihilators imply a common annihilator
-- statement:
--   For $0\le\alpha<\pi$, the relaxed-state set consists of the matrices $\Omega_n(\alpha)=\{e^{i\alpha/2}P+e^{-i\alpha/2}Q:P,Q\succeq0,\ \operatorname{Tr}(P)+\operatorname{Tr}(Q)=1\}$. Here $P,Q$ are square complex matrices of the indicated dimension; these phase-weighted sums need not be density matrices.
--
--   Let $n\ge1$, let $\mathcal A\subset M_n(\mathbb C)$ be a complex linear subspace, and let $0\le\alpha<\pi$. Then
--
--   $$[\exists\rho\in\Omega_n(\alpha)\ \forall A\in\mathcal A:\operatorname{Tr}(\rho A)=0]
--   \iff[\forall A\in\mathcal A\ \exists\rho\in\Omega_n(\alpha):\operatorname{Tr}(\rho A)=0].$$
--
--   Thus separate relaxed annihilators can be replaced by one common annihilator for a complex subspace.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 8, Lemma 13

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Lemma 13, PDF p.8: reversal of quantifiers over a complex linear subspace. -/
theorem commonAnnihilator {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Submodule ℂ (Mat ι)) (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    (∃ R ∈ omega (ι := ι) a, ∀ X ∈ M, (R * X).trace = 0) ↔
    (∀ X ∈ M, ∃ R ∈ omega (ι := ι) a, (R * X).trace = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
