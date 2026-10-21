-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_cloning_block_normalization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.cloning_block_normalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:57:35.470918+00:00
-- url     : https://prove2.me/theorems/b84ddfe4-d40d-4804-972b-d9f16aa38c0e
-- title:
--   Block normalization is equivalent to operational cloning feasibility
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   Let the five equality patterns of $(i,j,k)$ be $xxx,xxy,xyx,xyy,xyz$, with $xyz$ absent at $d=2$. Their multiplicities are $d$, $d(d-1)$ for each of the middle three, and $d(d-1)(d-2)$. Write $s_\ell^\nu=(n_\ell/d)r_\ell^\nu$ for the scaled positive multiplicity blocks in sectors $\nu=\alpha,\beta,\gamma$. Alpha blocks are $2\times2$; beta and gamma are supported on their respective plus and minus coordinates. Gamma is absent at $d=2$. Let $\mathcal M_d$ be the unswapped block set satisfying
--   $$\sum_{\ell,\nu}d_\nu(s_\ell^\nu)_{++}=d_+,\qquad\sum_{\ell,\nu}d_\nu(s_\ell^\nu)_{--}=d_-,$$
--   where $d_\pm=d(d\pm1)/2$, $d_\alpha=d$, $d_\beta=d(d-1)(d+2)/2$, and $d_\gamma=d(d+1)(d-2)/2$. Blocks for absent sectors and classes are zero.
--
--   For every positive block array with the indicated supports, let $R(s)$ be its concrete Schur expansion and classical-wire lift. Then
--   $$R(s)\text{ is a feasible cloning instrument}\iff s\in\mathcal M_d.$$
--   Conversely, every diagonal, covariant, simultaneously relabel invariant feasible cloning instrument is $R(s)$ for some $s\in\mathcal M_d$. This is an operational equivalence; exchange symmetry is not imposed on $\mathcal M_d$.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 6, §V, Eqs.(49)–(55): equivalent deterministic normalization in blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF pp.6-7, Eqs.(49)-(55): equivalent
normalization and completeness relative to the genuine operational cloning domain.
No exchange symmetry is imposed on the block set. -/
theorem cloning_block_normalization (d : ℕ) (hd : 2 ≤ d) :
    (∀ b : BlockArray, BlockShape d b →
      (IsReplicationStrategy .cloning (expandBlocks d b) ↔ b ∈ cloningBlockSet d)) ∧
    (∀ R : ReplicationChoiArray d, IsReplicationStrategy .cloning R → dephaseClassicalOutput R = R →
      BlocksCommuteWithRotations (diagonalBlocks R) → RelabelInvariant (diagonalBlocks R) →
      ∃ b ∈ cloningBlockSet d, R = expandBlocks d b) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
