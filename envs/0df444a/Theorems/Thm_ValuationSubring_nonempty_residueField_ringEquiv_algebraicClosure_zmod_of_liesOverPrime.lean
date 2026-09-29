-- Prove2me | Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
-- name    : ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/0f9ba805-0434-575a-bbeb-f245063b0289
-- title:
--   Residue field of a place of ℚ̄ above q
-- statement:
--   Let $A$ be a valuation subring of the field $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, let $q$ be a natural number which is prime, and assume that $A$ lies over $q$ in the sense of the project predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), namely that the image of $q$ in $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ belongs to `A.nonunits`, the set of elements of $A$ that are not units of $A$. The conclusion asserts that the type of ring isomorphisms between the residue field of the local ring $A$ and $\mathrm{AlgebraicClosure}(\mathbb{Z}/q\mathbb{Z})$ is nonempty; that is, there exists an isomorphism of rings $A/\mathfrak m_A \cong \overline{\mathbb F}_q$. Only the existence of such an isomorphism is asserted: no compatibility with the $\mathbb Z/q\mathbb Z$-algebra structures, and no canonical choice, is recorded in the statement.
--
--   This is the standard identification of the residue field of a place of $\overline{\mathbb Q}$ above a rational prime $q$ with an algebraic closure of $\mathbb F_q$. It is used wherever the project needs to transfer data between residue characteristic $q$ coefficients and $\overline{\mathbb F}_q$, for instance in the treatment of mod $p$ modular forms and of Galois representations attached to finite flat group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime] (hA : A.LiesOverPrime q) :
    Nonempty (IsLocalRing.ResidueField A ≃+* AlgebraicClosure (ZMod q)) := by sorry
