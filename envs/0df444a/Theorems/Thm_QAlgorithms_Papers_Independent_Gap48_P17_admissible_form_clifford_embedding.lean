-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_admissible_form_clifford_embedding
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.admissible_form_clifford_embedding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:11:03.006141+00:00
-- url     : https://prove2.me/theorems/c24d2b64-db26-42fd-ba62-8726ea977a6a
-- title:
--   Definition 2.1 consequence: invariance and image symmetry of Clifford embedding
-- statement:
--   Let $V=\mathbb R^{p,q}\ne0$ and $S$ be the full real Clifford spinor. Choose its compatible semispinor splitting when the even restriction is reducible. Let $\beta$ be admissible with sign witnesses $\tau,\sigma\in\{1,-1\}$. Then $\beta$ is invariant, $j_\rho(\beta)(v)(s,t)=\beta(\rho(v)s,t)$ is equivariant, and
--   $$j_\rho(\beta)(v)(t,s)=\tau\sigma\,j_\rho(\beta)(v)(s,t).$$
--   For $\beta\ne0$ this map is injective. In the split case its image forms have isotropy sign $-\iota(\beta)$: the halves are isotropic for sign $-1$ and mutually orthogonal for sign $1$. At $\beta=0$ all map and signed-image assertions remain valid, while injectivity is not asserted. This explicitly repairs the printed use of the word embedding at zero.
--
--   The witnesses mean $\beta(\rho(v)s,t)=\tau\beta(s,\rho(v)t)$ and $\beta(t,s)=\sigma\beta(s,t)$ for all $v,s,t$. Admissibility also requires the stated orthogonality or isotropy condition for the chosen halves whenever a split exists.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 18, Definition 2.1 consequence: invariance and image symmetry of Clifford embedding

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Definition 2.1 consequence, PDF p. 18. Printed: every admissible beta gives
an embedding. Changed: injectivity requires beta != 0; all other clauses include
zero. Why: zero is admissible under the printed conditions and gives the zero map
on nonzero V. No other hypothesis or conclusion is changed. -/
theorem admissible_form_clifford_embedding (p q : ℕ) (hd : 0 < p + q)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S)
    (splitting : Option (SpinSplitting rho)) (hs : CompleteSplitting rho splitting)
    (b : LinearMap.BilinForm ℝ S) (hb : FormAdmissible rho splitting b)
    (tau sigma : ℝ) (hsgn : FormSigns rho b tau sigma) :
    b ∈ invariantForms rho ∧ cliffordForm rho b ∈ equivariantForms rho ∧
    (b ≠ 0 → Function.Injective (cliffordForm rho b)) ∧
    (∀ v s t, cliffordForm rho b v t s = (tau * sigma) * cliffordForm rho b v s t) ∧
    (∀ h : SpinSplitting rho, splitting = some h →
      ∀ i : ℝ, FormIsotropy h.grading b i →
        ∀ v, FormIsotropy h.grading (cliffordForm rho b v) (-i)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
