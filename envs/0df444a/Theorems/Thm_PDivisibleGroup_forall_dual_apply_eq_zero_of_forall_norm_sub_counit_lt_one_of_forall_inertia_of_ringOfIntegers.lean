-- Prove2me | Theorems.Thm_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers
-- name    : PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/9d3bb09e-e778-5d01-98ac-7554e1e319bc
-- title:
--   Inertia-invariant functionals vanish on unit-section Tate vectors
-- statement:
--   Fix a prime $p$, an intermediate field $K$ of $\mathbb{Q}_p \subseteq \overline{\mathbb{Q}}_p$ (here `PadicAlgCl p`) that is finite-dimensional over $\mathbb{Q}_p$, and write $\mathcal{O}_K$ for [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with $K$, viewed as a $\mathbb{Z}_p$-subalgebra. Let $G$ be a $p$-divisible group of height $h$ over $\mathcal{O}_K$, i.e. a system of cocommutative Hopf algebras $G_v =$ `G.level v` that are finite free over $\mathcal{O}_K$ of rank $p^{vh}$, together with surjective coalgebra-algebra maps $G_{v+1} \to G_v$ whose kernels are the $p^v$-torsion ideals. Its group of $\overline{\mathbb{Q}}_p$-points `G.Points` is the direct limit of the groups of $\mathcal{O}_K$-algebra homomorphisms $G_v \to \overline{\mathbb{Q}}_p$ under convolution, and [`TateModule p`](def/EllipticCurve_TateModule.html#L15) of that group is the group of sequences $(z_n)$ with $p^n z_n = 0$ and $p z_{n+1} = z_n$, a $\mathbb{Z}_p$-module on which the $\mathcal{O}_K$-algebra automorphisms of $\overline{\mathbb{Q}}_p$ act componentwise via `G.tateModuleRep`. Let $f$ be a $\mathbb{Z}_p$-linear functional on this Tate module satisfying: for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}_p$ lying in the inertia subgroup attached to the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) (the image of the inertia subgroup of the decomposition subgroup over $\mathbb{Q}_p$) and every $\mathcal{O}_K$-algebra automorphism $\tau$ agreeing with $\sigma$ at every point, $f(\tau z) = f(z)$ for all $z$. Let $x$ be an element of the Tate module such that for every $n$ there exist a level $w$ and a point $g \colon G_w \to \overline{\mathbb{Q}}_p$ whose image in the direct limit is $x_n$ and which satisfies $\lVert g(a) - \varepsilon(a) \rVert < 1$ for all $a \in G_w$, where $\varepsilon$ is the counit followed by the structural map $\mathcal{O}_K \to \overline{\mathbb{Q}}_p$. Then $f(x) = 0$.
--
--   This is the inertia-invariant form of the statement that a Galois-equivariant functional on the Tate module of a $p$-divisible group over $\mathcal{O}_K$ annihilates the Tate module of the connected part, the sequences whose components are represented by points congruent to the unit section. It is the local input used in the form with the valuation in place of the norm, [`PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_valuation_sub_counit_lt_one_of_forall_inertia`](thm.html#PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_valuation_sub_counit_lt_one_of_forall_inertia).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (f : TateModule p (G.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] ℤ_[p])
    (hf : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) →
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ z : TateModule p (G.Points (PadicAlgCl p)),
          f (G.tateModuleRep (PadicAlgCl p) τ z) = f z)
    (x : TateModule p (G.Points (PadicAlgCl p)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (g : G.Point (PadicAlgCl p) w),
      G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
        (x : ℕ → G.Points (PadicAlgCl p)) n ∧
      ∀ a : G.level w, ‖PDivisibleGroup.Point.toAlgHom g a -
        algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) :
    f x = 0 := by sorry
