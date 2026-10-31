-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_symplectic_direct_sum_bases
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.symplectic_direct_sum_bases
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:15:24.391668+00:00
-- url     : https://prove2.me/theorems/99880e6b-85f6-4724-bbd1-abda382451f7
-- title:
--   Unnumbered symplectic direct sum of bases and matrices
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   Suppose $V=W_1\oplus W_2$, with the summands $\Omega$-orthogonal and $A$-invariant. Let $(e_1,\ldots,e_{2k})$ and $(f_1,\ldots,f_{2l})$ be symplectic bases of the summands, representing the restrictions by $M_1$ and $M_2$, each written in first-half/second-half sectors $M_{a,pq}$, $p,q\in\{1,2\}$. Then the explicitly concatenated basis
--   $$(e_1,\ldots,e_k,f_1,\ldots,f_l,e_{k+1},\ldots,e_{2k},f_{l+1},\ldots,f_{2l})$$
--   is symplectic and represents $A$ by
--   $$M_1\diamond M_2=\begin{pmatrix}M_{1,11}&0&M_{1,12}&0\\0&M_{2,11}&0&M_{2,12}\\M_{1,21}&0&M_{1,22}&0\\0&M_{2,21}&0&M_{2,22}\end{pmatrix}.$$
--   Either summand may be zero-dimensional.
--
--
--   This fixes the coordinate permutation used for every later symplectic block sum.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 2, Unnumbered symplectic direct sum of bases and matrices

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse only the pinned accepted substrate, with definitionally identical coordinate models.
-- The imported symplectic predicate preserves -Omega0, equivalent to preserving Omega0.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

/-- PDF p.2: the explicitly concatenated basis is symplectic and represents
A by A1 diamond A2, in grouped order rather than ordinary block-diagonal order. -/
theorem symplectic_direct_sum_bases {n k l : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (W1 W2 : Submodule ℝ (RVec n)) (hsum : W1 ⊔ W2 = ⊤) (hd : Disjoint W1 W2)
    (ho : ∀ v ∈ W1, ∀ w ∈ W2, omegaR v w = 0)
    (b1 : Module.Basis (Coord k) ℝ W1) (b2 : Module.Basis (Coord l) ℝ W2)
    (M1 : GroupedRealMatrix k) (M2 : GroupedRealMatrix l)
    (hb1 : ∀ i j, omegaR (b1 i).val (b1 j).val =
      groupedOmega (Pi.single i 1) (Pi.single j 1))
    (hb2 : ∀ i j, omegaR (b2 i).val (b2 j).val =
      groupedOmega (Pi.single i 1) (Pi.single j 1))
    (ha1 : ∀ j, A.mulVec (b1 j).val = ∑ i, M1 i j • (b1 i).val)
    (ha2 : ∀ j, A.mulVec (b2 j).val = ∑ i, M2 i j • (b2 i).val) :
    ∃ b : Module.Basis ((Fin k ⊕ Fin l) ⊕ (Fin k ⊕ Fin l)) ℝ (RVec n),
      (∀ i, b (Sum.inl (Sum.inl i)) = (b1 (Sum.inl i)).val) ∧
      (∀ i, b (Sum.inl (Sum.inr i)) = (b2 (Sum.inl i)).val) ∧
      (∀ i, b (Sum.inr (Sum.inl i)) = (b1 (Sum.inr i)).val) ∧
      (∀ i, b (Sum.inr (Sum.inr i)) = (b2 (Sum.inr i)).val) ∧
      (∀ i j, omegaR (b i) (b j) = groupedOmega (Pi.single i 1) (Pi.single j 1)) ∧
      ∀ j, A.mulVec (b j) = ∑ i, symplecticDiamond M1 M2 i j • b i := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
