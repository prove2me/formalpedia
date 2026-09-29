-- Prove2me | Theorems.Thm_ValuationSubring_isIntegral_of_forall_mem
-- name    : ValuationSubring.isIntegral_of_forall_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/7d557ada-a7e6-5a54-9a0b-7e59c6e2f933
-- title:
--   Integrality from valuation rings of F with trace V
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $V$ be a valuation subring of $K$, and suppose $F$ is also given as a $V$-algebra compatibly, i.e. the scalar actions of $V$ on $F$ through $K$ and directly agree (`IsScalarTower V K F`). Let $f$ be an element of $F$. Assume that $f$ lies in every valuation subring $B$ of $F$ whose trace on $K$ is exactly $V$, the condition on $B$ being stated elementwise: for all $x \in K$, the image $\mathrm{algebraMap}_{K,F}(x)$ lies in $B$ if and only if $x \in V$. Then $f$ is integral over $V$: it is a root of some monic polynomial with coefficients in $V$. No assumption is made that $K$ is the fraction field of $V$, that $F$ is algebraic over $K$, or that valuation subrings of $F$ with trace $V$ exist; the hypothesis quantifies over all of them, possibly vacuously.
--
--   This refines the classical description of the integral closure as the intersection of the valuation rings containing a given ring: only those valuation rings of $F$ whose intersection with $K$ is precisely $V$ need to be tested. It is used to convert an exhaustive list of the valuation subrings of $F$ lying over $V$ into integrality over $V$, in the analysis of prolongations of places in [`ModularCurve.PlaceSpecialization`](def/ModularCurve_PlaceSpecialization.html#L13).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isIntegral_of_forall_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isIntegral_of_forall_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    (V : ValuationSubring K) [Algebra V F] [IsScalarTower V K F] (f : F)
    (h : ∀ B : ValuationSubring F, (∀ x : K, algebraMap K F x ∈ B ↔ x ∈ V) → f ∈ B) :
    IsIntegral V f := by sorry
