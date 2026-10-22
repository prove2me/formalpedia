-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_definite_pin_form_admissible
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.definite_pin_form_admissible
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:06:43.656833+00:00
-- url     : https://prove2.me/theorems/84e62c41-add6-431b-85f8-fed664b32cd8
-- title:
--   Lemma 3.7
-- statement:
--   Let $V=\mathbb R^{p,q}\ne0$ have definite signature, and let $S$ be its full irreducible real Clifford module. Let $h$ be a positive definite symmetric real bilinear form invariant under every unit-vector Clifford action, equivalently under $\operatorname{Pin}(V)$. Then $h$ is admissible and
--   $$\tau(h)=\begin{cases}-1,&q=0,\\1,&p=0,\end{cases}\qquad\sigma(h)=1.$$
--   When the even restriction splits into the chosen compatible semispinor summands, these are mutually $h$-orthogonal, so $\iota(h)=1$. No isotropy sign is assigned in the irreducible-even case.
--
--   The type $\tau$ is the adjoint sign of Clifford vector multiplication relative to $h$, the symmetry $\sigma$ is the exchange sign of $h$, and isotropy $\iota=+1$ means that the two chosen halves are mutually orthogonal.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 24, Lemma 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lemma 3.7, PDF p. 24: the definite Pin-invariant positive scalar product has all
three asserted invariants, with isotropy asserted only for a genuine splitting. -/
theorem definite_pin_form_admissible (p q : ℕ) (hd : 0 < p + q)
    (hdefinite : p = 0 ∨ q = 0)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S)
    (splitting : Option (SpinSplitting rho)) (hs : CompleteSplitting rho splitting)
    (b : LinearMap.BilinForm ℝ S) (hsymm : b.IsSymm)
    (hpositive : ∀ s : S, s ≠ 0 → 0 < b s s) (hpin : PinInvariant rho b) :
    FormAdmissible rho splitting b ∧
    FormSigns rho b (if q = 0 then -1 else 1) 1 ∧
    (∀ h : SpinSplitting rho, splitting = some h → FormIsotropy h.grading b 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
