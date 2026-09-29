-- Prove2me | Theorems.Thm_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
-- name    : PadicAlgCl.mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/85444ca3-b7d7-5443-9f6a-280a54a66605
-- title:
--   Inertia in Gal(ℚ̄ₚ/ℚₚ) via norms
-- statement:
--   Let $p$ be a prime and let $\sigma$ be an automorphism of the field `PadicAlgCl p` (an algebraic closure of $\mathbb{Q}_p$ carrying a valuation with values in $\mathbb{R}_{\geq 0}$) as an algebra over $\mathbb{Q}_p$. Write $A$ for [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20), the valuation subring attached to that valuation, i.e. the elements of norm at most $1$. The subgroup $A.\mathrm{inertiaSubgroupIn}\ \mathbb{Q}_p$ of the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p` is by definition the image, under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}_p$ into the full automorphism group, of the inertia subgroup of $A$ over $\mathbb{Q}_p$ (the kernel of the action of the decomposition subgroup on the residue field of $A$). The assertion is an equivalence: $\sigma$ lies in this subgroup if and only if for every $x$ in `PadicAlgCl p` with $\|x\| \leq 1$ one has $\|\sigma x - x\| < 1$.
--
--   This is the translation of the inertia condition for the algebraic closure of $\mathbb{Q}_p$ — stabilising the valuation ring and acting trivially on the residue field $\overline{\mathbb{F}}_p$ — into an inequality between $p$-adic absolute values, in the form used throughout the local $p$-adic part of the argument. It is invoked in the construction of Frobenius lifts modulo inertia for finite extensions and in the criterion for a representation with trivial inertia action to have an integral structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one.lean

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PadicAlgCl.mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
    (p : ℕ) [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔
      ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by sorry
