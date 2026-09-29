-- Prove2me | Theorems.Thm_ValuationSubring_irreducible_natCast_comap_of_forall_smul_eq
-- name    : ValuationSubring.irreducible_natCast_comap_of_forall_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/d0d28d21-1770-56b4-a70a-3e2e0c00fd90
-- title:
--   ℓ is irreducible in V∩ E when E is decomposition-fixed
-- statement:
--   Let $N$ be a field which is a number field and is Galois over $\mathbb{Q}$, let $V$ be a valuation subring of $N$, and let $\ell$ be a prime number whose image in $N$ lies in `V.nonunits`, i.e. belongs to $V$ and is not a unit of $V$ (equivalently, lies in the maximal ideal of $V$). Let $E$ be an intermediate field of $N/\mathbb{Q}$, and assume that every $\mathbb{Q}$-algebra automorphism $\tau$ of $N$ with $\tau \bullet V = V$ for the pointwise action of the Galois group on valuation subrings — that is, every element of the decomposition group of $V$ — fixes $E$ pointwise: $\tau x = x$ for all $x \in E$. The conclusion is that the image of the natural number $\ell$ in the valuation subring of $E$ obtained by pulling $V$ back along the structure map $E \to N$, namely `V.comap (algebraMap E N)` $= V \cap E$, is an irreducible element of that ring. Since that ring is a valuation ring of the number field $E$, irreducibility of $\ell$ says exactly that $\ell$ is a uniformiser, so the associated prime of $E$ above $\ell$ is unramified over $\mathbb{Q}$.
--
--   This is the standard fact that the decomposition field of a prime is unramified over the base with residue degree one, phrased valuation-theoretically: any subfield fixed by the decomposition group of $V$ sees $\ell$ as a uniformiser of $V \cap E$. It is used in [`ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup`](thm.html#ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup) to produce a discrete valuation ring with uniformiser $\ell$ inside a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_irreducible_natCast_comap_of_forall_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise

theorem ValuationSubring.irreducible_natCast_comap_of_forall_smul_eq (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (V : ValuationSubring N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ((ℓ : ℕ) : N) ∈ V.nonunits)
    (E : IntermediateField ℚ N)
    (hE : ∀ τ : N ≃ₐ[ℚ] N, τ • V = V → ∀ x ∈ E, τ x = x) :
    Irreducible ((ℓ : ℕ) : V.comap (algebraMap E N)) := by sorry
