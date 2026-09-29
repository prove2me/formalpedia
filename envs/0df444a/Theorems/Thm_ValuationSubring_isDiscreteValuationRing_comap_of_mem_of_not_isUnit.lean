-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_mem_of_not_isUnit
-- name    : ValuationSubring.isDiscreteValuationRing_comap_of_mem_of_not_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/7134764b-e1d0-58a7-be41-0ea83380d826
-- title:
--   Pullback of a discrete valuation ring along a field embedding
-- statement:
--   Let $K$ and $F$ be fields, let $W$ be a valuation subring of $K$ whose underlying ring $\uparrow W$ is a discrete valuation ring, and let $\iota \colon F \to K$ be a ring homomorphism. Suppose there is an element $t \in F$ with $t \neq 0$ such that $\iota(t)$ lies in $W$ and the corresponding element $\langle \iota(t)\rangle$ of $\uparrow W$ is not a unit of $W$. Then the valuation subring $W.\mathrm{comap}\ \iota$ of $F$, i.e. the preimage $\{x \in F : \iota(x) \in W\}$ regarded as a valuation subring of $F$, has underlying ring a discrete valuation ring. Thus the hypotheses are: $W$ is a discretely valued valuation subring of $K$, and the valuation of $W$ is non-trivial on the image of $F$, witnessed by the single non-zero element $t$ whose image lies in the maximal ideal of $W$; the conclusion is the instance $\mathrm{IsDiscreteValuationRing}$ for $\iota^{-1}(W)$.
--
--   This is the standard statement that a discrete valuation restricts to a discrete valuation on a subfield on which it is non-trivial (the value group being a non-zero subgroup of $\mathbb{Z}$, hence infinite cyclic). It is used in the analysis of models of modular curves at full level, in the rigid-chart and descent steps for the $\ell = 2$ and $\ell = 3$ cases and in the general assembly of those steps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_comap_of_mem_of_not_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_comap_of_mem_of_not_isUnit
    (K F : Type) [Field K] [Field F] (W : ValuationSubring K) [IsDiscreteValuationRing ↥W]
    (ι : F →+* K) (t : F) (ht : ι t ∈ W) (ht' : ¬ IsUnit (⟨ι t, ht⟩ : ↥W)) (ht0 : t ≠ 0) :
    IsDiscreteValuationRing ↥(W.comap ι) := by sorry
