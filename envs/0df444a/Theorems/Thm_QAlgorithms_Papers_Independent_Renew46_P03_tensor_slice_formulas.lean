-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P03_tensor_slice_formulas
-- name    : QAlgorithms.Papers.Independent.Renew46.P03.tensor_slice_formulas
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:52:46.12976+00:00
-- url     : https://prove2.me/theorems/665a5b92-b4b4-4312-8ea9-893e24f64f06
-- title:
--   Lemma 2.2: tensor slices, reconstruction and slice adjoints
-- statement:
--   Let $H_1,H_2$ be separable complex Hilbert spaces with complete countable orthonormal bases $(\phi_i)_{i\in I}$ and $(\psi_j)_{j\in J}$. Write $T=H_1\widehat\otimes H_2$ for the completed Hilbert tensor product, with $H_1$ first. The slice $P_i:T\to H_2$ is constructed as the adjoint of $y\mapsto\phi_i\otimes y$ and has the source's defining expansion
--
--   $$P_i\alpha=\sum_j\langle\phi_i\otimes\psi_j,\alpha\rangle\psi_j.$$
--
--   For all $x\in H_1$, $y,\beta\in H_2$, and $\alpha\in T$,
--
--   $$P_i(x\otimes y)=\langle\phi_i,x\rangle y,\qquad \sum_i\phi_i\otimes P_i\alpha=\alpha,$$
--   $$P_i^*\beta=\sum_j\langle\psi_j,\beta\rangle\phi_i\otimes\psi_j.$$
--
--   All three displayed series converge in the Hilbert norm. These formulas give the coordinate slices, tensor reconstruction, and slice adjoints.
-- source:
--   Operator Isomorphisms on Hilbert Space Tensor Products, arXiv:2010.15901v1, PDF p. 8, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P03

universe u v

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

/-- Lemma 2.2, PDF p.8: the defining slice expansion, action on simple tensors,
reconstruction, and adjoint expansion. The repeated printed part label (b)
is read as (c), following the proof. Every infinite sum converges in norm. -/
theorem tensor_slice_formulas
    {H1 : Type u} {H2 : Type v}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1] [CompleteSpace H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]
    [TopologicalSpace.SeparableSpace H1] [TopologicalSpace.SeparableSpace H2]
    {ι : Type u} {κ : Type v} [Countable ι] [Countable κ]
    (b1 : HilbertBasis ι ℂ H1) (b2 : HilbertBasis κ ℂ H2) :
    (∀ i (a : HilbertTensor H1 H2),
      HasSum (fun j => inner ℂ (tensorVector (b1 i) (b2 j)) a • b2 j)
        (tensorSlice (b1 i) a)) ∧
    (∀ i (x : H1) (y : H2),
      tensorSlice (b1 i) (tensorVector x y) = inner ℂ (b1 i) x • y) ∧
    (∀ a : HilbertTensor H1 H2,
      HasSum (fun i => tensorVector (b1 i) (tensorSlice (b1 i) a)) a) ∧
    (∀ i (y : H2),
      HasSum (fun j => inner ℂ (b2 j) y • tensorVector (b1 i) (b2 j))
        ((tensorSlice (b1 i)).adjoint y)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P03

end
