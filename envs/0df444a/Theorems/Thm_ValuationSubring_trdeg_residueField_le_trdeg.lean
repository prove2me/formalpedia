-- Prove2me | Theorems.Thm_ValuationSubring_trdeg_residueField_le_trdeg
-- name    : ValuationSubring.trdeg_residueField_le_trdeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/bd0fe58c-bc83-56b3-9760-47a92cefc4bd
-- title:
--   Residue transcendence degree bounded by trdeg_K L
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A$ be a valuation subring of $L$. Write $B =$ `A.comap (algebraMap K L)` for the valuation subring of $K$ obtained by pulling $A$ back along the structure map $K \to L$. Assume the residue field $\kappa(A) =$ `IsLocalRing.ResidueField A` is given the structure of an algebra over $\kappa(B)$, subject to the compatibility hypothesis `hcompat`: for every $b \in B$, the structure map $\kappa(B) \to \kappa(A)$ carries the residue class of $b$ to the residue class in $\kappa(A)$ of the element of $A$ given by the image $\mathrm{algebraMap}\ K\ L\ (b)$ (which lies in $A$ precisely because $b \in B$). Then the transcendence degree of $\kappa(A)$ over $\kappa(B)$ is at most the transcendence degree of $L$ over $K$, as an inequality of cardinals in the sense of `Algebra.trdeg`. The hypothesis on the algebra structure is stated for an arbitrary compatible homomorphism rather than only for the canonical residue-field embedding induced by $B \hookrightarrow A$.
--
--   This is the residue-field half of Abhyankar's inequality, the other half being the bound on the rational rank of the quotient of value groups; classically it appears as a corollary to the comparison of valuations in a field extension. It is used here through [`ValuationSubring.le_trdeg_residueField_comap_of_le_trdeg_residueField`](thm.html#ValuationSubring.le_trdeg_residueField_comap_of_le_trdeg_residueField), in the valuation-theoretic input to arguments about dominant morphisms of varieties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_trdeg_residueField_le_trdeg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.trdeg_residueField_le_trdeg
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Algebra (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : A.comap (algebraMap K L),
      algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩) :
    Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) ≤ Algebra.trdeg K L := by sorry
