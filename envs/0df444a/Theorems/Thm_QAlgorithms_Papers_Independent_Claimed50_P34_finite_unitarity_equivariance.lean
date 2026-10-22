-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P34_finite_unitarity_equivariance
-- name    : QAlgorithms.Papers.Independent.Claimed50.P34.finite_unitarity_equivariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:50:58.992664+00:00
-- url     : https://prove2.me/theorems/7409ee78-cfdc-4a9b-bf5b-872f11af109d
-- title:
--   Finite-dimensional Jamiolkowski permutations are unitary and equivariant
-- statement:
--   Let $H_1,H_2$ be finite-dimensional complex Hilbert spaces. Give their continuous complex duals the conjugate-dual Hilbert structure, so that $\langle\bar x,\bar y\rangle=\langle y,x\rangle$. On the Hilbert tensor space $H_1\otimes H_1^*\otimes H_2\otimes H_2^*$ define $J$ and $\widetilde J$ by complex-linear extension of
--
--   $$
--   J(x\otimes\bar x'\otimes y\otimes\bar y')=x\otimes\bar y'\otimes y\otimes\bar x',\qquad
--   \widetilde J(x\otimes\bar x'\otimes y\otimes\bar y')=x\otimes y\otimes\bar y'\otimes\bar x'.
--   $$
--
--   Both maps are bijections preserving the Hermitian inner product. If $g=(A,A',B,B')$ is any element of $GL(H_1)^2\times GL(H_2)^2$, its source action sends the four factors to $Ax,\overline{A'x'},By,\overline{B'y'}$. Let $g_J$ and $g_{\widetilde J}$ act on the corresponding target slots in the permuted order. Then, for every tensor $v$,
--
--   $$
--   J(gv)=g_JJ(v),\qquad \widetilde J(gv)=g_{\widetilde J}\widetilde J(v).
--   $$
--
--   These are the unitary and symmetry properties of the finite-dimensional state–map correspondences in the paper's tensor realization.
--
--   **Formalization Note** Orthonormal tensor coefficients are represented by a Euclidean space with four index slots. The dual slots carry entrywise conjugated matrices, with no inverse or transpose. Arbitrary finite dimensions are quantified; any finite-dimensional Hilbert spaces admit these orthonormal coordinates. No linear Riesz identification is introduced.
-- source:
--   On the relation between states and maps in infinite dimensions, arXiv:0706.2617v1, PDF p. 6, Theorem 1; equations (12)–(17)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P34

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P34

/-- PDF p.6, Theorem 1, with the finite-dimensional standing assumption on p.3.
In the orthonormal tensor coordinates of (12)–(17), both specified complex-linear
maps are bijective and preserve the Hermitian inner product. They intertwine all
four invertible factor actions; the barred factors carry conjugate actions.
Arbitrary finite dimensions, including zero, are permitted. No identification of
H with H* is used: the two target slot polarities differ even though their
coordinate index types have the same shape. -/
theorem finite_unitarity_equivariance (n m : ℕ) :
    Function.Bijective (jamiolkowskiTensor (n := n) (m := m)) ∧
    Function.Bijective (twistedJamiolkowski (n := n) (m := m)) ∧
    (∀ v w : FourTensor n n m m,
      inner ℂ (jamiolkowskiTensor v) (jamiolkowskiTensor w) = inner ℂ v w ∧
      inner ℂ (twistedJamiolkowski v) (twistedJamiolkowski w) = inner ℂ v w) ∧
    (∀ (A Aprime : (Matrix (Fin n) (Fin n) ℂ)ˣ)
        (B Bprime : (Matrix (Fin m) (Fin m) ℂ)ˣ) (v : FourTensor n n m m),
      jamiolkowskiTensor
          (factorAction A.val (dualMatrix Aprime.val) B.val (dualMatrix Bprime.val) v) =
        factorAction A.val (dualMatrix Bprime.val) B.val (dualMatrix Aprime.val)
          (jamiolkowskiTensor v) ∧
      twistedJamiolkowski
          (factorAction A.val (dualMatrix Aprime.val) B.val (dualMatrix Bprime.val) v) =
        factorAction A.val B.val (dualMatrix Bprime.val) (dualMatrix Aprime.val)
          (twistedJamiolkowski v)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P34

end
