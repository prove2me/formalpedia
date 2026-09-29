-- Prove2me | Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional
-- name    : ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/4118bd97-1814-50b2-88cc-dfcf9afeab5b
-- title:
--   A discrete valuation ring extends along a finite field extension
-- statement:
--   Let $F$ and $E$ be fields with $E$ an $F$-algebra that is finite-dimensional over $F$, and let $W$ be a valuation subring of $F$ whose underlying ring is a discrete valuation ring. Then there exists a valuation subring $V$ of $E$ such that: the underlying ring of $V$ is a discrete valuation ring; for every $x \in F$ belonging to $W$, the image $\operatorname{algebraMap} F E\, x$ lies in $V$; and for every element $x$ of $W$ lying in the maximal ideal of the local ring $W$, the image of $x$ under $F \to E$ lies in `V.nonunits`, i.e. is a non-unit of $V$ (equivalently, has valuation strictly less than one). Thus $V$ is a discrete valuation subring of $E$ dominating $W$: it contains the image of $W$ and its non-units contain the image of the maximal ideal of $W$. No separability assumption is made on $E/F$; the statement asserts existence of one such $V$, not uniqueness, nor the sharper equality $V \cap F = W$.
--
--   This is the existence of an extension of a discrete valuation to a finite extension field, in the form of a dominating discrete valuation subring, with inseparable extensions allowed. It is used downstream to produce discrete valuation rings with prescribed fraction field and residue-field properties, for instance in the statements on faithfully flat extensions of discrete valuation rings and on valuation subrings of a local ring with finite residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (W : ValuationSubring F) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring E, IsDiscreteValuationRing ↥V ∧
      (∀ x : F, x ∈ W → algebraMap F E x ∈ V) ∧
      (∀ x : ↥W, x ∈ maximalIdeal ↥W → algebraMap F E (x : F) ∈ V.nonunits) := by sorry
