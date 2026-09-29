-- Prove2me | Theorems.Thm_ValuationSubring_exists_algEquiv_residue_pow_eq_of_nonunits
-- name    : ValuationSubring.exists_algEquiv_residue_pow_eq_of_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/04422310-27f0-5fa4-b964-649cf17a57d3
-- title:
--   Frobenius powers on residues realised in Gal(ℚ̄/K)
-- statement:
--   Let $K$ be an intermediate field of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` over $\mathbb Q$ that is finite-dimensional over $\mathbb Q$, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $q$ be a prime number whose image in $\overline{\mathbb Q}$ lies in `A.nonunits`, i.e. is a non-unit of $A$ (equivalently, lies in the maximal ideal of $A$), let $L$ be an intermediate field of $\overline{\mathbb Q}$ over $K$ with $L/K$ finite, and let $m$ be a natural number. Assume that raising to the $q^m$-th power fixes the residues of the elements of $K \cap A$: for every $x \in K$ with $x \in A$ one has $\mathrm{res}(x)^{q^m} = \mathrm{res}(x)$, where $\mathrm{res}$ denotes the residue map of the local ring $A$ onto its residue field. Then there exists a $K$-algebra automorphism $\delta$ of $\overline{\mathbb Q}$ such that, first, for every $x \in L$ one has $x \in A$ if and only if $\delta x \in A$, and second, for every $x \in L$ with $x \in A$ and $\delta x \in A$ one has $\mathrm{res}(\delta x)^{q^m} = \mathrm{res}(x)$.
--
--   This is the surjectivity of the decomposition group onto the Galois group of the residue extension, in the form of Hilbert's ramification theory, stated at a finite level inside $\overline{\mathbb Q}$: the prescribed power map $t \mapsto t^{q^m}$ on residues, trivial on the residues coming from $K$, is inverted on the residues of $L$ by an element of $\mathrm{Gal}(\overline{\mathbb Q}/K)$ preserving $A$ on $L$. It feeds the construction of Frobenius elements attached to a valuation subring lying over a prime, and the localisation argument at nodes of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algEquiv_residue_pow_eq_of_nonunits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_algEquiv_residue_pow_eq_of_nonunits
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] (m : ℕ)
    (hfix : ∀ (x : AlgebraicClosure ℚ) (hxK : x ∈ K) (hxA : x ∈ A),
      IsLocalRing.residue ↥A ⟨x, hxA⟩ ^ (q ^ m) = IsLocalRing.residue ↥A ⟨x, hxA⟩) :
    ∃ δ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ,
      (∀ x : AlgebraicClosure ℚ, x ∈ L → (x ∈ A ↔ δ x ∈ A)) ∧
      ∀ (x : AlgebraicClosure ℚ) (hxL : x ∈ L) (hxA : x ∈ A) (hδ : δ x ∈ A),
        IsLocalRing.residue ↥A ⟨δ x, hδ⟩ ^ (q ^ m) = IsLocalRing.residue ↥A ⟨x, hxA⟩ := by sorry
