-- Prove2me | Theorems.Thm_PDivisibleGroup_hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers
-- name    : PDivisibleGroup.hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/f4d5abf8-c2e0-5217-be66-61b1dd0068a5
-- title:
--   Unramified Tate module forces dimension zero (Tate)
-- statement:
--   Fix a prime $p$, and let $K$ be an intermediate field of the extension $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$ (written `PadicAlgCl p`) which is finite-dimensional over $\mathbb{Q}_p$; write $\mathcal{O}_K$ for [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the $\mathbb{Z}_p$-subalgebra of $\overline{\mathbb{Q}}_p$ obtained as the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with $K$. Let $h$ be a natural number and $Q$ a $p$-divisible group over $\mathcal{O}_K$ of height $h$ in the sense of [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): a system of commutative, cocommutative Hopf algebras $Q_v$ over $\mathcal{O}_K$, each finite and free of rank $p^{vh}$, with surjective coalgebra-algebra transition maps $Q_{v+1} \to Q_v$ whose kernels are the $p^v$-torsion ideals. Assume that whenever a $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}_p$ and an $\mathcal{O}_K$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}_p$ agree at every point, and $\sigma$ lies in `(padicIntegers p).inertiaSubgroupIn ℚ_[p]`, the image in the full automorphism group of the inertia subgroup over $\mathbb{Q}_p$ of the valuation subring of $\overline{\mathbb{Q}}_p$, then $\tau$ acts as the identity on the Tate module of $Q(\overline{\mathbb{Q}}_p)$, that is on the group of sequences $(x_n)$ of points with $p^n x_n = 0$ and $p x_{n+1} = x_n$. The conclusion is `Q.HasDimension 0`: for every $v$ the cotangent module of the augmentation ideal of $Q_v$ admits an $\mathcal{O}_K$-linear isomorphism onto the zero module $\mathrm{Fin}\,0 \to \mathcal{O}_K/(p^v)$, i.e. it vanishes.
--
--   This is Tate's result that the Galois action on the Tate module determines the dimension of a $p$-divisible group over the ring of integers of a $p$-adic field, in the special case at hand: an unramified Tate module forces the dimension to be zero. It is used to show that all levels of such a group are formally étale, in [`PDivisibleGroup.forall_formallyEtale_level_of_forall_inertia_tateModuleRep_eq_of_ringOfIntegers`](thm.html#PDivisibleGroup.forall_formallyEtale_level_of_forall_inertia_tateModuleRep_eq_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (Q : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (hQ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) →
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ z : TateModule p (Q.Points (PadicAlgCl p)), Q.tateModuleRep (PadicAlgCl p) τ z = z) :
    Q.HasDimension 0 := by sorry
