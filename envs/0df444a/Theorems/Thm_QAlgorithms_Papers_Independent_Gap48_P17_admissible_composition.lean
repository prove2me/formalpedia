-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_admissible_composition
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.admissible_composition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:11:33.984805+00:00
-- url     : https://prove2.me/theorems/2b7d203c-ec13-4f72-959c-1badb33db1da
-- title:
--   Definition 2.2 consequence: composition multiplies invariants
-- statement:
--   For the full real Clifford spinor of a nonzero pseudo-Euclidean space, choose a compatible semispinor split when it exists. Let $\beta$ be admissible and let $A$ be $\beta$-admissible. Then $A$ is invariant, $\beta_A(s,t)=\beta(As,t)$ is invariant and admissible, and its signs satisfy
--   $$\tau(\beta_A)=\tau(\beta)\tau(A),\qquad\sigma(\beta_A)=\sigma(\beta)\sigma_\beta(A),\qquad\iota(\beta_A)=\iota(\beta)\iota(A).$$
--   The last identity is asserted only for the chosen split. Each equation means that the product of any sign witnesses is a sign witness for the composite; it does not require a unique sign for a zero form. This gives a relational version of the source's multiplicativity rule.
--
--   Here the form type is defined by $\beta(\rho(v)s,t)=\tau(\beta)\beta(s,\rho(v)t)$, and its symmetry by $\beta(t,s)=\sigma(\beta)\beta(s,t)$. The endomorphism type means $\rho(v)A=\tau(A)A\rho(v)$, and $\beta(As,t)=\sigma_\beta(A)\beta(s,At)$. Isotropy $+1$ means orthogonal halves for forms and preserved halves for endomorphisms; $-1$ means isotropic halves and interchanged halves, respectively.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 18, Definition 2.2 consequence: composition multiplies invariants

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Definition 2.2 consequence, PDF p. 18. Composition multiplies all defined signs;
this uses witnesses, and does not assign unique invariants to a zero composite. -/
theorem admissible_composition (p q : ℕ) (hd : 0 < p + q)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S)
    (splitting : Option (SpinSplitting rho)) (hs : CompleteSplitting rho splitting)
    (b : LinearMap.BilinForm ℝ S) (hb : FormAdmissible rho splitting b)
    (A : Module.End ℝ S) (hA : EndAdmissible rho splitting b A) :
    A ∈ schurAlgebra rho ∧ formCompose b A ∈ invariantForms rho ∧
    FormAdmissible rho splitting (formCompose b A) ∧
    (∀ tau sigma tauA sigmaA : ℝ,
      FormSigns rho b tau sigma → EndSigns rho b A tauA sigmaA →
        FormSigns rho (formCompose b A) (tau * tauA) (sigma * sigmaA)) ∧
    (∀ h : SpinSplitting rho, splitting = some h →
      ∀ i iA : ℝ, FormIsotropy h.grading b i → EndIsotropy h.grading A iA →
        FormIsotropy h.grading (formCompose b A) (i * iA)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
