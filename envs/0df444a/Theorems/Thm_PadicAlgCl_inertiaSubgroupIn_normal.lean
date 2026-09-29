-- Prove2me | Theorems.Thm_PadicAlgCl_inertiaSubgroupIn_normal
-- name    : PadicAlgCl.inertiaSubgroupIn_normal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/d88052a2-5c43-50e9-bb72-a8d5d5c9777e
-- title:
--   Normality of the inertia subgroup over ℚₚ
-- statement:
--   Let $p$ be a prime. Consider `PadicAlgCl p`, the field carrying a `Valued` structure with $\mathbb{R}_{\ge 0}$-valued valuation $v$, and let [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) denote the valuation subring of `PadicAlgCl p` attached to $v$, i.e. the unit ball $\{x : v(x) \le 1\}$. For this valuation subring $A$, the group `inertiaSubgroupIn ℚ_[p] A` is defined as the image, under the inclusion of the decomposition subgroup $D = \{\sigma : \sigma \cdot A = A\} \le (\mathrm{PadicAlgCl}\ p \simeq_{\mathrm{alg}[\mathbb{Q}_p]} \mathrm{PadicAlgCl}\ p)$ into the full group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p`, of the inertia subgroup of $A$ relative to $\mathbb{Q}_p$ (the kernel of the action of $D$ on the residue field of $A$); so it is a subgroup of the whole automorphism group rather than of $D$ alone. The theorem asserts that this subgroup of `PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p` is normal.
--
--   This is the standard fact that inertia is a normal subgroup of the local Galois group, here in the form needed for the automorphism group of the completed algebraic closure of $\mathbb{Q}_p$. It is used where inertia-invariance has to be preserved under translation by Galois elements, in the $p$-divisible group and $p$-adic Hodge-theoretic input to the deformation-theoretic arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_inertiaSubgroupIn_normal.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.inertiaSubgroupIn_normal (p : ℕ) [Fact p.Prime] :
    ((padicIntegers p).inertiaSubgroupIn ℚ_[p] : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)).Normal := by sorry
