-- Prove2me | Theorems.Thm_ValuationSubring_nonempty_residueField_algEquiv_algebraicClosure_galoisField
-- name    : ValuationSubring.nonempty_residueField_algEquiv_algebraicClosure_galoisField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/9e73947f-a23e-57fd-8cb6-0dc1610f451b
-- title:
--   Residue field at a place of ℚ̄ is ̄mathbb F_{q²}
-- statement:
--   Let $q$ be a prime number, let $P$ be a valuation subring of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$, and assume that $P$ lies over $q$ in the sense of the project predicate `LiesOverPrime`, that is, the image of $q$ in $\overline{\mathbb Q}$ lies in the set of non-units of $P$ (so $q$ belongs to the maximal ideal of the local ring $P$). Let $\iota : \mathrm{GF}(q,2) \to \kappa(P)$ be a ring homomorphism from the field with $q^2$ elements to the residue field $\kappa(P)$ of $P$, and regard $\kappa(P)$ as an algebra over $\mathrm{GF}(q,2)$ via $\iota$. Then the type of $\mathrm{GF}(q,2)$-algebra isomorphisms from $\kappa(P)$ to the algebraic closure of $\mathrm{GF}(q,2)$ is nonempty: there exists an isomorphism $\kappa(P) \cong \overline{\mathbb F_{q^2}}$ of fields compatible with $\iota$ and with the structure map of the algebraic closure. No canonicity of the isomorphism is asserted, only its existence.
--
--   This identifies the residue field of a place of $\overline{\mathbb Q}$ above $q$ with an algebraic closure of $\mathbb F_{q^2}$, once an embedding of $\mathbb F_{q^2}$ into that residue field has been fixed; uniqueness of algebraic closures over a base is the classical input. It is used in the treatment of Tate curves at full level, where reduction maps on torsion must be compared with Galois modules defined over $\overline{\mathbb F_{q^2}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_nonempty_residueField_algEquiv_algebraicClosure_galoisField.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.nonempty_residueField_algEquiv_algebraicClosure_galoisField
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField P) := ι.toAlgebra
    Nonempty (IsLocalRing.ResidueField P ≃ₐ[GaloisField q 2] AlgebraicClosure (GaloisField q 2)) := by sorry
