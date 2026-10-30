-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma2_leftRight
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma2_leftRight
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:25:53.307132+00:00
-- url     : https://prove2.me/theorems/bb674c8d-1dc7-499b-9ed3-72c8e4fdac02
-- title:
--   Lemma 2: finite left-right representation of every linear map
-- statement:
--   Let $n>0$ and let $\Phi:M_n(\mathbb C)\to M_n(\mathbb C)$ be complex-linear. There are an integer $0\le m\le n^2$ and matrices $A_\nu,B_\nu\in M_n(\mathbb C)$, chosen independently of $X$, such that
--
--   $$
--   \Phi(X)=\sum_{\nu=1}^{m}A_\nu X B_\nu^\dagger\qquad(X\in M_n(\mathbb C)).
--   $$
--
--   The empty family is allowed for the zero map. This is a finite left-right representation of every linear operator on matrix space.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 6, Lemma 2: finite left-right representation of every linear map

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.6, Lemma 2 Eq.(12). Families are chosen before the arbitrary operator X. -/
theorem lemma2_leftRight (n : ℕ) (hn : 0 < n) (Phi : EndMat n) :
    ∃ m : ℕ, m ≤ n^2 ∧ ∃ A B : Fin m → Mat n,
      ∀ X : Mat n, Phi X = ∑ v, A v * X * (B v)ᴴ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
