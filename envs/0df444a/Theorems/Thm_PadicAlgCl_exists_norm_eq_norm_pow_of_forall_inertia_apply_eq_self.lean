-- Prove2me | Theorems.Thm_PadicAlgCl_exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
-- name    : PadicAlgCl.exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/a539f2b3-3c3c-56d8-9fc1-5df28714372e
-- title:
--   Inertia-fixed elements have norm a power of ‖p‖
-- statement:
--   Let $p$ be a prime number and let $x$ be a nonzero element of `PadicAlgCl p`, the project's algebraic closure of $\mathbb{Q}_p$, equipped with its valuation $v$ into $\mathbb{R}_{\ge 0}$ and the associated norm. Write [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) for the valuation subring of `PadicAlgCl p` attached to $v$, and let its inertia subgroup in $\mathbb{Q}_p$, in the sense of `inertiaSubgroupIn`, be the image in the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p` of the inertia subgroup of that valuation subring under the inclusion of its decomposition subgroup. Assume that every automorphism $\iota$ of `PadicAlgCl p` over $\mathbb{Q}_p$ lying in this inertia subgroup satisfies $\iota x = x$. The conclusion is that there exists an integer $n$ with $\|x\| = \|(p : \mathrm{PadicAlgCl}\ p)\|^{\,n}$, the integer power of the norm of the image of the natural number $p$; since that norm equals $p^{-1}$, this says exactly that $\|x\|$ lies in the value group $p^{\mathbb{Z}}$ of $\mathbb{Q}_p$ itself.
--
--   This is the statement that the maximal unramified extension of $\mathbb{Q}_p$ inside $\overline{\mathbb{Q}}_p$, i.e. the fixed field of inertia, has the same value group as $\mathbb{Q}_p$, so that its ramification index over $\mathbb{Q}_p$ is $1$. It is used in the construction of an inertia-invariant lattice: in [`PadicComplex.exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers`](thm.html#PadicComplex.exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers), where norms of inertia-fixed scalars must be recognised as powers of $\|p\|$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self.lean

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

theorem PadicAlgCl.exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
    (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx0 : x ≠ 0)
    (hx : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι x = x) :
    ∃ n : ℤ, ‖x‖ = ‖(p : PadicAlgCl p)‖ ^ n := by sorry
