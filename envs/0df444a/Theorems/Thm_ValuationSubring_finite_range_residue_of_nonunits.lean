-- Prove2me | Theorems.Thm_ValuationSubring_finite_range_residue_of_nonunits
-- name    : ValuationSubring.finite_range_residue_of_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/50b5fe31-1822-5f07-a844-fb06fb3d7c3e
-- title:
--   Finiteness of the residues of A ∩ L in κ(A)
-- statement:
--   Let $K$ be an intermediate field of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` over $\mathbb Q$ which is finite-dimensional over $\mathbb Q$, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $q$ be a natural number which is prime, and assume that the image of $q$ in $\overline{\mathbb Q}$ lies in `A.nonunits`, the set of elements of the field whose $A$-valuation is strictly less than $1$ (equivalently, elements of $A$ that are not units of $A$). Let $L$ be an intermediate field of $\overline{\mathbb Q}$ over $K$ which is finite-dimensional over $K$. The assertion is that the set of values taken by the residue map of the local ring $A$, as $x$ ranges over the subtype of those $x \in \overline{\mathbb Q}$ satisfying both $x \in L$ and $x \in A$ (the element $x$ being regarded as an element of $A$ via its membership), is a finite subset of the residue field of $A$. In other words, the image of $A \cap L$ in $\kappa(A)$ is finite.
--
--   The residues of the elements of $A \cap L$ form a finite subfield-like subset of $\kappa(A)$, reflecting the fact that $A \cap L$ is the localisation of the ring of integers of the number field $L$ at a prime above $q$, whose residue field is finite. It is used in the analysis of the local structure of a modular curve at a node, in [`ModularCurve.NodeLocalized.exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem`](thm.html#ModularCurve.NodeLocalized.exists_ringHom_ker_eq_centred_of_height_one_of_natCast_notMem), where finiteness of the residue field at hand makes two embeddings of it into an algebraic closure differ by a power of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_finite_range_residue_of_nonunits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.finite_range_residue_of_nonunits
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] :
    (Set.range fun x : {x : AlgebraicClosure ℚ // x ∈ L ∧ x ∈ A} =>
      IsLocalRing.residue ↥A ⟨x.1, x.2.2⟩).Finite := by sorry
