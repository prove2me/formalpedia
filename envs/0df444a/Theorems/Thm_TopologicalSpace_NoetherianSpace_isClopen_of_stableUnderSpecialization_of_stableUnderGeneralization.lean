-- Prove2me | Theorems.Thm_TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization
-- name    : TopologicalSpace.NoetherianSpace.isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/24f1df5f-6063-5ef6-b617-874244f7b118
-- title:
--   Specialisation- and generalisation-stable subsets of noetherian sober spaces are clopen
-- statement:
--   Let $X$ be a topological space in a universe $u$ which is noetherian (every open subset is compact, in Mathlib's `NoetherianSpace`) and quasi-sober (every irreducible closed subset has a generic point), and let $s \subseteq X$ be a subset. Assume that $s$ is stable under specialisation, i.e. if $x \rightsquigarrow y$ and $x \in s$ then $y \in s$, and stable under generalisation, i.e. if $x \rightsquigarrow y$ and $y \in s$ then $x \in s$. The conclusion is that $s$ is clopen: $s$ is both closed and open in $X$. No further hypothesis on $X$ (separation, or being a spectrum) is imposed; in particular both the hypotheses and the conclusion are symmetric under passage to the complement, since the complement of a specialisation-stable set is generalisation-stable and conversely.
--
--   A standard point-set statement about noetherian sober spaces, applicable in particular to $\operatorname{Spec}$ of a noetherian ring: there, a subset of the spectrum closed under passing both to specialisations and to generalisations is open and closed. It is used to show that a function on the spectrum of a noetherian ring taking equal values at any pair $\mathfrak q' \rightsquigarrow \mathfrak q$ is locally constant, which is how local constancy of Euler characteristics in a locally trivial family is obtained in [`AlgebraicGeometry.OModulePresheaf.exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem TopologicalSpace.NoetherianSpace.isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {s : Set X}
    (h₁ : StableUnderSpecialization s) (h₂ : StableUnderGeneralization s) : IsClopen s := by sorry
