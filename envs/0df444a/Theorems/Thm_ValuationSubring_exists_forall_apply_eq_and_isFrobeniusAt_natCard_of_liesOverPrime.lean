-- Prove2me | Theorems.Thm_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
-- name    : ValuationSubring.exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/cb37047f-234d-5773-b1de-bb62e5496c15
-- title:
--   Relative Frobenius at a place of ℚ̄ over a number field
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. the image of $q$ in $\overline{\mathbb{Q}}$ lies in the set of nonunits of $A$ (so $q$ belongs to the maximal ideal of the local ring $A$), and let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$. Then there exist a natural number $d$ and an automorphism $\sigma$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ such that: $d > 0$; the image of $\{a \in A : a \in K\}$ under the residue map $A \to A/\mathfrak{m}_A$ — that is, the range of $a \mapsto \mathrm{residue}(a)$ on the subtype of elements of $A$ lying in $K$ — has cardinality exactly $q^d$ (as a `Nat.card`, so the assertion includes its finiteness); $\sigma z = z$ for every $z \in K$; and `A.IsFrobeniusAt σ (q ^ d)` holds, meaning that $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ (so $\sigma$ preserves $A$) and the resulting action of $\sigma$ on the residue field of $A$ is $x \mapsto x^{q^d}$.
--
--   This is the existence of a Frobenius element relative to a number field $K$ at a place of $\overline{\mathbb{Q}}$ above $q$: the decomposition group of $A$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/K)$ maps onto the Galois group of the residue extension, and the statement simultaneously records that the residue field of $A \cap K$ is finite of cardinality $q^d$ with $d \geq 1$. It is used in the analysis of specialisations of places on modular curves, where the residue field of $A \cap K$ must be identified with $\mathbb{F}_{q^d}$ and a Frobenius acting trivially on $K$ is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    ∃ (d : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), 0 < d ∧
      Nat.card (Set.range fun a : {a : ↥A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue ↥A a.1) = q ^ d ∧
      (∀ z ∈ K, σ z = z) ∧ A.IsFrobeniusAt σ (q ^ d) := by sorry
