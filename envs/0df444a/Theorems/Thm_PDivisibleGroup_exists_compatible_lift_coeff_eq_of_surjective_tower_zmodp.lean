-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp
-- name    : PDivisibleGroup.exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/5cca2904-8a6c-505b-9637-351997ed9dd0
-- title:
--   Compatible normalised lifts of Dieudonné covector components
-- statement:
--   Fix a commutative ring $\mathcal O$ and a prime $p$ such that $p$ is a non-zero-divisor in $\mathcal O$, equipped with an $\mathcal O$-algebra structure on $\mathbb Z/p$ whose structure map has kernel the ideal $(p)$, and assume $\mathcal O$ is adically complete for $(p)$. Let $(Ge_v)_{v\in\mathbb N}$ be commutative rings that are Hopf algebras over $\mathbb Z/p$ and module-finite over $\mathbb Z/p$, with bialgebra maps $se_v\colon Ge_{v+1}\to Ge_v$; let $(Et_v)_{v\in\mathbb N}$ be commutative rings that are Hopf algebras over $\mathcal O$, finite and free as $\mathcal O$-modules, with bialgebra maps $st_v\colon Et_{v+1}\to Et_v$, each surjective; and let $\theta^e_v\colon \mathbb Z/p\otimes_{\mathcal O}Et_v\to Ge_v$ be bijective bialgebra maps such that $\mathrm{id}\otimes st_v$ followed by $\theta^e_v$ equals $\theta^e_{v+1}$ followed by $se_v$. Finally let $m_v$ lie in [`Deformation.DieudonneModule (ZMod p) p (Ge v)`](def/Dieudonne_WittHomColimit.html#L234), the direct limit over $n$, along the shift maps, of the additive subgroup [`Deformation.wittHom`](def/Dieudonne_WittVectorHom.html#L246) of those truncated Witt vectors $x\in W_n(Ge_v)$ satisfying $W_n(\Delta)(x)=W_n(\iota_1)(x)+W_n(\iota_2)(x)$ for the comultiplication $\Delta$ and the two inclusions $Ge_v\to Ge_v\otimes Ge_v$, and assume $m_{v+1}\mapsto m_v$ under the map induced by $se_v$. The conclusion asserts the existence of elements $\hat c_{k,v}\in Et_v$ ($k,v\in\mathbb N$) with $st_v(\hat c_{k,v+1})=\hat c_{k,v}$ and $\mathcal O$-counit $\varepsilon(\hat c_{k,v})=0$, such that for every $v$ there are $n$ and $u\in$ [`Deformation.wittHom (ZMod p) p n (Ge v)`](def/Dieudonne_WittVectorHom.html#L246) whose image in the direct limit is $m_v$, with $u_{\,n-1-k}=\theta^e_v(1\otimes\hat c_{k,v})$ for all $k<n$, and $\theta^e_v(1\otimes\hat c_{k,v})=0$ for all $k\ge n$.
--
--   This is the lifting step in Fontaine's construction of Honda systems (Astérisque 47–48, Ch. IV n° 1.6): the covector components of a compatible family of Dieudonné-module elements of the special fibre are lifted, compatibly along the tower and normalised to have vanishing counit, to the étale Hopf algebras over $\mathcal O$; the existence of such lifts at all levels simultaneously is of Mittag-Leffler type, the relevant surjections being $Et_v\twoheadrightarrow \mathbb Z/p\otimes_{\mathcal O}Et_v\cong Ge_v$. It is used by [`Deformation.HondaSystem.exists_splitCoordinates_lawful_normalForm`](thm.html#Deformation.HondaSystem.exists_splitCoordinates_lawful_normalForm), where the lifted components are assembled into convergent $p$-adic series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v

theorem PDivisibleGroup.exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]

    (Ge : ℕ → Type v) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
    (Et : ℕ → Type u) [∀ v, CommRing (Et v)] [∀ v, HopfAlgebra 𝓞 (Et v)] [∀ v, Module.Free 𝓞 (Et v)] [∀ v, Module.Finite 𝓞 (Et v)]
    (st : ∀ v, Et (v + 1) →ₐc[𝓞] Et v) (hst : ∀ v, Function.Surjective (st v))
    (θe : ∀ v, ZMod p ⊗[𝓞] Et v →ₐc[ZMod p] Ge v) (hθe : ∀ v, Function.Bijective (θe v))
    (hθe_comp : ∀ v, (θe v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (st v)) = (se v).comp (θe (v + 1)))

    (m : ∀ v, Deformation.DieudonneModule (ZMod p) p (Ge v))
    (hm : ∀ v, Deformation.DieudonneModule.map (ZMod p) p (se v) (m (v + 1)) = m v) :
    ∃ ĉ : ℕ → ∀ v, Et v,
      (∀ k v, st v (ĉ k (v + 1)) = ĉ k v) ∧
      (∀ k v, Coalgebra.counit (R := 𝓞) (ĉ k v) = 0) ∧
      (∀ v, ∃ (n : ℕ) (u : Deformation.wittHom (ZMod p) p n (Ge v)),
        Deformation.DieudonneModule.of (ZMod p) p (Ge v) n u = m v ∧
        (∀ (k : ℕ) (hk : k < n), (u : TruncatedWittVector p n (Ge v)).coeff ⟨n - 1 - k, by omega⟩ =
           θe v ((1 : ZMod p) ⊗ₜ[𝓞] ĉ k v)) ∧
        (∀ k, n ≤ k → θe v ((1 : ZMod p) ⊗ₜ[𝓞] ĉ k v) = 0)) := by sorry
