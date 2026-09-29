-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_restrictNormal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/fcdeeddc-4d3c-52a5-88c8-f22590130d3d
-- title:
--   Inertia elements lift along normal subextensions
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra such that $L/K$ is Galois, let $M$ be an intermediate field of $L/K$ that is normal over $K$, and let $A$ be a valuation subring of $L$. Write $B := A.\mathrm{comap}\,(\mathrm{algebraMap}\ M\ L)$ for the valuation subring $A \cap M$ of $M$ obtained by pulling $A$ back along the inclusion $M \hookrightarrow L$. Here, for a valuation subring $V$ of a field $F$ Galois over $E$, `inertiaSubgroupIn` denotes the image in $F \simeq_{\mathrm{alg}[E]} F$ of the inertia subgroup of $V$ under the inclusion of the decomposition subgroup of $V$ over $E$, i.e. the set of those $E$-automorphisms of $F$ that stabilise $V$ and act trivially on its residue field. The hypothesis is that $\tau : M \simeq_{\mathrm{alg}[K]} M$ lies in the inertia subgroup of $B$ over $K$ in this sense. The conclusion is that there exists a $K$-automorphism $\sigma$ of $L$ lying in the inertia subgroup of $A$ over $K$ whose restriction to $M$, taken as `σ.restrictNormal M`, equals $\tau$. Thus restriction maps the inertia subgroup of $A$ onto that of $B$.
--
--   This is the inertia analogue, for arbitrary valuation subrings and possibly infinite Galois extensions, of the classical statement that the decomposition group of a valuation surjects onto the decomposition group of its restriction to a normal subextension (Hilbert's ramification theory). It is used in the construction of inertia elements acting in a prescribed way on cyclotomic subextensions, via [`ValuationSubring.exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension`](thm.html#ValuationSubring.exists_mem_inertiaSubgroupIn_forall_apply_algebraMap_eq_of_isCyclotomicExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_restrictNormal_eq
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [Normal K M]
    (A : ValuationSubring L) (τ : M ≃ₐ[K] M)
    (hτ : τ ∈ (A.comap (algebraMap M L)).inertiaSubgroupIn K) :
    ∃ σ : L ≃ₐ[K] L, σ ∈ A.inertiaSubgroupIn K ∧ σ.restrictNormal M = τ := by sorry
