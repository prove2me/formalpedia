-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P20_left_tight_identities
-- name    : QAlgorithms.Papers.Independent.Renew46.P20.left_tight_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:23:30.356556+00:00
-- url     : https://prove2.me/theorems/41afefb1-7767-40ba-8af9-d4d5f74f2e03
-- title:
--   Equivalent left-tight frame identities
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space with a fixed orthonormal basis, let $(\Omega,\Sigma,\mu)$ be a finite measure space, and let $A_\omega\in\operatorname{Lin}(H)$ be a measurable operator family with integrable frame projectors. Let $K\ge0$ be an operator on $H$. Write $|A\rangle\!\rangle=\sum_{i,j}A_{ij}|i\rangle|j\rangle$ for unnormalized vectorization, $T$ for basis transpose, and $*$ for entrywise conjugation. The following three identities are equivalent:
--
--   $$
--   \int_\Omega |A_\omega\rangle\!\rangle\langle\!\langle A_\omega|\,d\mu=I\otimes K;
--   $$
--   $$
--   \forall X\in\operatorname{Lin}(H),\quad
--   \int_\Omega A_\omega X A_\omega^\dagger\,d\mu
--   =\operatorname{Tr}(XK^T)I;
--   $$
--   $$
--   \int_\Omega A_\omega\otimes A_\omega^*\,d\mu
--   =|I\rangle\!\rangle\langle\!\langle K^T|.
--   $$
--
--   All displayed integrands are integrable. These identities identify the frame operator, its associated averaging map, and its matrix representation. Neither invertibility of $K$ nor probability normalization of $\mu$ is required.
-- source:
--   Realization schemes for quantum instruments in finite dimensions, arXiv:0810.3211v4, PDF p. 17, Definition 4 and Eq.(85)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P20

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P40 (operatorKet)

namespace QAlgorithms.Papers.Independent.Renew46.P20

/-- PDF p.17, Definition 4 and both identities in Eq.(85).
A finite measure and an integrable measurable frame are used; K may be singular
or zero, and the measure need not be a probability measure. -/
theorem left_tight_identities
    {I W : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [MeasurableSpace W]
    (mu : Measure W) [IsFiniteMeasure mu] (A : W → Matrix I I ℂ)
    (hA : StronglyMeasurable A)
    (hframe : Integrable (fun w => pureDensity (operatorKet (A w))) mu)
    (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    (frameOperator mu A = Matrix.kronecker (1 : Matrix I I ℂ) K ↔
      ∀ X : Matrix I I ℂ,
        Integrable (fun w => A w * X * (A w)ᴴ) mu ∧
        (∫ w, A w * X * (A w)ᴴ ∂mu) =
          (X * K.transpose).trace • (1 : Matrix I I ℂ)) ∧
    (frameOperator mu A = Matrix.kronecker (1 : Matrix I I ℂ) K ↔
      Integrable (fun w => Matrix.kronecker (A w)
        (fun i j => conj (A w i j))) mu ∧
      (∫ w, Matrix.kronecker (A w) (fun i j => conj (A w i j)) ∂mu) =
        (fun p q => operatorKet (1 : Matrix I I ℂ) p *
          conj (operatorKet K.transpose q))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P20

end
