-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P79_lemma_2_3_1
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P79.lemma_2_3_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:19:14.311199+00:00
-- url     : https://prove2.me/theorems/fa50c532-634d-4535-a9ce-a281b897510a
-- title:
--   Minimal idempotents: global product descriptions
-- statement:
--   Let $k$ be algebraically closed of characteristic zero, let $M$ be an irreducible affine algebraic monoid, let $G$ be its unit group, and let $e$ be an idempotent which is the unique idempotent of $eMe$. Write $M_e^\ell=\{x:xe=e\}$, $M_e^r=\{x:ex=e\}$, $M_e=M_e^\ell\cap M_e^r$, and $G_e^\ell,G_e^r,G_e$ for their intersections with $G$. The left and right group centralizers are $C_G^\ell(e)=\{g:ge=ege\}$ and $C_G^r(e)=\{g:eg=ege\}$. Products below are products of subsets of $M$, $Me$ and $eM$ are the principal ideals, and $\ker(M)$ is the least nonempty two-sided ideal. Then
--
--   $$\begin{gathered}
--   Me=C_G^r(e)e,\quad M=C_G^r(e)M_e^\ell,\quad eM=eC_G^\ell(e),\quad M=M_e^rC_G^\ell(e),\\
--   M_e^re=G_e^re,\quad M_e^r=G_e^rM_e,\quad eM_e^\ell=eG_e^\ell,\quad M_e^\ell=M_eG_e^\ell,\\
--   M=C_G^r(e)M_eG_e^\ell=C_G^\ell(e)M_eG_e^r,\\
--   \ker(M)=C_G^r(e)eG_e^\ell=C_G^\ell(e)eG_e^r,\\
--   M_0^r=M_0^\ell=M_0=M.
--   \end{gathered}$$
--
--   Here $M_0^r=\{x:xe\in C_G^r(e)e\}$, $M_0^\ell=\{x:ex\in eC_G^\ell(e)\}$ and $M_0=M_0^r\cap M_0^\ell$. The local product loci therefore cover the whole monoid at a minimal idempotent.
--
--   **Formalization Note** Equalities are stated on closed-point loci, which determine reduced subvarieties over $k$. No quotient or geometric isomorphism is replaced by a point-set bijection.
-- source:
--   Local structure of algebraic monoids, arXiv:0709.1255v2, PDF p. 14, Lemma 2.3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P79

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open CategoryTheory.MonObj

open scoped CategoryTheory.MonObj Pointwise

universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P79

variable (k : Type u) [Field k]

variable {k}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Lemma 2.3.1, PDF p. 14, all four parts and both left/right counterparts.
These are equalities of the closed-point loci of the indicated reduced
subvarieties; no quotient is replaced by a point bijection. The affine standing
hypothesis of Sections 1-2 is retained. -/
theorem lemma_2_3_1 [IsAlgClosed k] [CharZero k]
    (M : KScheme k) [MonObj M] [IsVariety k M] [IrreducibleSpace M.left]
    [IsAffine M.left] (e : MonoidSchemePoint M) (he : IsIdempotentPoint M e)
    (hmin : IsMinimalIdempotent M e) :
    (rightIdealPoints M e = groupCentralizerPoints M e 1 * {e} ∧
      Set.univ = groupCentralizerPoints M e 1 * stabilizerPoints M e 0 ∧
      leftIdealPoints M e = {e} * groupCentralizerPoints M e 0 ∧
      Set.univ = stabilizerPoints M e 1 * groupCentralizerPoints M e 0) ∧
    (stabilizerPoints M e 1 * {e} = groupStabilizerPoints M e 1 * {e} ∧
      stabilizerPoints M e 1 = groupStabilizerPoints M e 1 * stabilizerPoints M e 2 ∧
      {e} * stabilizerPoints M e 0 = {e} * groupStabilizerPoints M e 0 ∧
      stabilizerPoints M e 0 = stabilizerPoints M e 2 * groupStabilizerPoints M e 0) ∧
    (Set.univ = groupCentralizerPoints M e 1 * stabilizerPoints M e 2 *
        groupStabilizerPoints M e 0 ∧
      Set.univ = groupCentralizerPoints M e 0 * stabilizerPoints M e 2 *
        groupStabilizerPoints M e 1 ∧
      kernelPoints M = groupCentralizerPoints M e 1 * {e} * groupStabilizerPoints M e 0 ∧
      kernelPoints M = groupCentralizerPoints M e 0 * {e} * groupStabilizerPoints M e 1) ∧
    (localOpenPoints M e 0 = Set.univ ∧
      localOpenPoints M e 1 = Set.univ ∧
      localOpenPoints M e 2 = Set.univ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P79

end
