-- Prove2me | Theorems.Thm_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
-- name    : Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/601d7704-6211-559b-8ea1-72b7535e1b49
-- title:
--   Mod p Hom-invariants unchanged by a finite-index Δ-stable subgroup
-- statement:
--   Let $p$ be a prime and $\Delta$ a finite group whose order is not divisible by $p$. Let $A$ be an additive abelian group with an action `act` of $\Delta$ by additive automorphisms, and assume $A$ has no $p$-torsion: $p\cdot a=0$ implies $a=0$. Let $B\le A$ be an additive subgroup of finite index which is stable under the action, in the sense that $a\in B$ implies $\mathrm{act}\,d\,a\in B$ for all $d\in\Delta$. Let $N$ be a representation of $\Delta$ on a finite-dimensional $\mathbb{Z}/p$-vector space $V_N$. Let $P_A$ be a representation of $\Delta$ on a finite-dimensional $\mathbb{Z}/p$-vector space $V_A$ together with a surjective additive map $\pi_A\colon A\to V_A$ whose kernel is exactly $pA$ (i.e. $\pi_A a=0$ iff $a=p a'$ for some $a'\in A$) and which is equivariant: $\pi_A(\mathrm{act}\,d\,a)=P_A(d)(\pi_A a)$. Let $P_B$, $V_B$, $\pi_B\colon B\to V_B$ be data of the same shape for $B$ with its restricted action. The conclusion is that the $\mathbb{Z}/p$-dimension of the invariants of $\mathrm{Hom}(N,P_A)$ equals that of the invariants of $\mathrm{Hom}(N,P_B)$; equivalently, $\dim_{\mathbb{F}_p}\mathrm{Hom}_\Delta(V_N,A/pA)=\dim_{\mathbb{F}_p}\mathrm{Hom}_\Delta(V_N,B/pB)$, the quotients being presented through $\pi_A$, $\pi_B$.
--
--   This is the torsion-free case of the statement that, for $p\nmid|\Delta|$, the multiplicity of a mod $p$ representation $N$ in $A/pA$ does not change when $A$ is replaced by a $\Delta$-stable subgroup of finite index — the form of Brauer's principle that reduction mod $p$ is independent of the chosen lattice that is needed here. It is applied to lattices such as a power of a maximal ideal inside a ring of integers and a normal-basis lattice, and is used in the computation of the dimension of $\Delta$-equivariant homomorphisms into principal units modulo a power of the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree.lean

import Mathlib
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Module

theorem Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
    {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ p ∣ Fintype.card Δ)
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A) (htf : ∀ a : A, p • a = 0 → a = 0)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) Δ VN)
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a))
    {VB : Type*} [AddCommGroup VB] [Module (ZMod p) VB] [FiniteDimensional (ZMod p) VB]
    (PB : Representation (ZMod p) Δ VB)
    (πB : B →+ VB) (hπB : Function.Surjective πB) (hkerB : ∀ b : B, πB b = 0 ↔ ∃ b' : B, p • b' = b)
    (hπBΔ : ∀ (d : Δ) (b : B), πB ⟨act d b, hB d b b.2⟩ = PB d (πB b)) :
    finrank (ZMod p) (N.linHom PA).invariants = finrank (ZMod p) (N.linHom PB).invariants := by sorry
