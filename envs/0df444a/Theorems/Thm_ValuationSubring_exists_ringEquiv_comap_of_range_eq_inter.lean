-- Prove2me | Theorems.Thm_ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter
-- name    : ValuationSubring.exists_ringEquiv_comap_of_range_eq_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/d4700d58-2eb8-599f-9e7d-d3e2902f2891
-- title:
--   Abstract presentations of the valuation subring A ∩ k₀
-- statement:
--   Let $F$ and $L$ be fields with $L$ an $F$-algebra, let $k_0$ be an intermediate field of $L/F$, and let $A$ be a valuation subring of $L$. Let $A_0$ be a commutative ring and $\iota : A_0 \to A$ an injective ring homomorphism, and assume that the image of $A_0$ read inside $L$, i.e. the range of $a \mapsto (\iota a : L)$, equals the intersection of $A$ with $k_0$ as subsets of $L$. The conclusion asserts the existence of a ring isomorphism $e$ from $A_0$ onto the valuation subring $A.\mathrm{comap}\,(\mathrm{algebraMap}\ k_0\ L)$ of $k_0$, the preimage of $A$ under the inclusion $k_0 \hookrightarrow L$, which is compatible with the two ways of reading elements in $L$: for every $a \in A_0$, the image in $L$ of $e\,a$ (first viewed as an element of $k_0$, then mapped by the structure morphism $k_0 \to L$) equals $(\iota a : L)$. The statement is an existence statement: no canonical choice of $e$ is singled out.
--
--   A transport lemma identifying any abstract presentation $(A_0,\iota)$ of the subring $A \cap k_0 \subseteq L$ with the valuation subring of $k_0$ obtained by pulling $A$ back along $k_0 \hookrightarrow L$. It lets statements about descent bases phrased through an abstract pair $(A_0,\iota)$ be matched with statements phrased through `ValuationSubring.comap`; it is used by the constructions of admissible constants for semistable models of full-level modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_ringEquiv_comap_of_range_eq_inter
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (k₀ : IntermediateField F L) (A : ValuationSubring L)
    (A₀ : Type*) [CommRing A₀] (ι : A₀ →+* ↥A) (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : L)) = (A : Set L) ∩ (k₀ : Set L)) :
    ∃ e : A₀ ≃+* ↥(A.comap (algebraMap ↥k₀ L)),
      ∀ a : A₀, algebraMap ↥k₀ L ((e a : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) = ((ι a : ↥A) : L) := by sorry
