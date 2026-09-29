-- Prove2me | Theorems.Thm_PrimeSpectrum_exists_locallyConstant_forall_apply_eq_iff
-- name    : PrimeSpectrum.exists_locallyConstant_forall_apply_eq_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/13b18740-ab28-5468-a181-40e6f81e7117
-- title:
--   Complete orthogonal idempotents give a locally constant function on Spec R
-- statement:
--   Let $R$ be a commutative ring and $\iota$ a finite index type, and let $e \colon \iota \to R$ be a family of elements of $R$ which is a complete orthogonal family of idempotents, i.e. each $e_i$ is idempotent, $e_i e_j = 0$ for $i \neq j$, and $\sum_{i \in \iota} e_i = 1$. The assertion is that there exists a locally constant map $f \colon \operatorname{Spec} R \to \iota$ from the prime spectrum of $R$, with its Zariski topology, to $\iota$ (with its discrete structure, as an element of `LocallyConstant (PrimeSpectrum R) ι`) such that for every index $i \in \iota$ and every prime $x$ of $\operatorname{Spec} R$ one has $f(x) = i$ if and only if $e_i$ does not belong to the prime ideal `x.asIdeal` underlying $x$. Thus the fibre of $f$ over $i$ is exactly the basic open set $D(e_i)$, and the $D(e_i)$ form a partition of $\operatorname{Spec} R$ into clopen pieces indexed by $\iota$.
--
--   This is one direction of the standard dictionary between locally constant $\iota$-valued functions on $\operatorname{Spec} R$ for finite $\iota$ and complete orthogonal families of idempotents in $R$, the other direction producing idempotents from such a function. It is used to convert an idempotent-theoretic witness back into a locally constant function, i.e. a section of a constant sheaf on $\operatorname{Spec} R$, in the descent argument [`Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary`](thm.html#Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PrimeSpectrum_exists_locallyConstant_forall_apply_eq_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open PrimeSpectrum

theorem PrimeSpectrum.exists_locallyConstant_forall_apply_eq_iff
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    ∃ f : LocallyConstant (PrimeSpectrum R) ι,
      ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal := by sorry
