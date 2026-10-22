-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_invariant_spaces_isomorphic
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.invariant_spaces_isomorphic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:59:54.82188+00:00
-- url     : https://prove2.me/theorems/e87aa4d0-e3b3-409c-a9c4-3eab58e258d8
-- title:
--   Corollary 1.6
-- statement:
--   For the nonzero real pseudo-Euclidean space $V$ and its full irreducible real Clifford module $S$, let $B$ be the space of invariant real bilinear forms on $S$, $J=\operatorname{Hom}_{\mathfrak{so}(V)}(V,(S\otimes S)^*)$, and $M=\operatorname{Hom}_{\mathfrak{so}(V)}(V\otimes S,S)$. Identify $V$ with $V^*$ by the metric. The three real vector spaces are isomorphic. More specifically, Clifford multiplication $\rho$ gives the linear isomorphism
--   $$j_\rho:B\longrightarrow J,\qquad j_\rho(\beta)(v)(s,t)=\beta(\rho(v)s,t).$$
--   Every equivariant embedding in $J$ has this form. This is the classification interface between brackets, bilinear invariants, and multiplications.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 14, Corollary 1.6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Corollary 1.6, PDF p. 14: all three spaces, including the specified j_rho isomorphism. -/
theorem invariant_spaces_isomorphic (p q : ℕ) (hd : 0 < p + q)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S) :
    (∃ e : invariantForms rho ≃ₗ[ℝ] equivariantForms rho,
      ∀ b : invariantForms rho, (e b).val = cliffordForm rho b.val) ∧
    Nonempty (equivariantForms rho ≃ₗ[ℝ] equivariantMultiplications rho) ∧
    (∀ j : equivariantForms rho, Function.Injective j.val →
      ∃ b : invariantForms rho, j.val = cliffordForm rho b.val) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
