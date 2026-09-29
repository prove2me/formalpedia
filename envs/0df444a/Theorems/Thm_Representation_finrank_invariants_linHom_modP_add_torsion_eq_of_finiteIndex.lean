-- Prove2me | Theorems.Thm_Representation_finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex
-- name    : Representation.finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/fac81f74-88cf-54b6-8565-d8f4eb472d5e
-- title:
--   Invariance of h_N under passage to a finite-index Δ-stable subgroup
-- statement:
--   Let $p$ be a prime, $\Delta$ a finite group whose order is not divisible by $p$, and $A$ an additive abelian group with an action $\mathrm{act} : \Delta \to \mathrm{AddAut}(A)$. Let $B \le A$ be a subgroup of finite index which is stable under the action, in the sense that $\mathrm{act}\,d\,a \in B$ whenever $a \in B$. Let $VN$ be a finite-dimensional $\mathbb{F}_p$-vector space carrying a representation $N$ of $\Delta$. Four further finite-dimensional $\mathbb{F}_p$-representations of $\Delta$ are given, presenting the four relevant subquotients: $PA$ on $VA$ together with a surjective additive map $\pi_A : A \to VA$ whose kernel is exactly $pA$ (i.e. $\pi_A a = 0$ iff $a = p\,a'$ for some $a'$) and which intertwines the action with $PA$; $TA$ on $WA$ together with an injective additive map $\iota_A : WA \to A$ whose image is exactly the $p$-torsion of $A$ and which intertwines $TA$ with the action; and likewise $PB$, $\pi_B : B \to VB$ and $TB$, $\iota_B : WB \to B$ for the subgroup $B$. The conclusion is the equality of $\mathbb{F}_p$-dimensions $$\dim \mathrm{Hom}_\Delta(VN, VA) + \dim \mathrm{Hom}_\Delta(VN, WB) = \dim \mathrm{Hom}_\Delta(VN, VB) + \dim \mathrm{Hom}_\Delta(VN, WA),$$ the spaces of $\Delta$-equivariant maps being realised as the invariants of the representations `N.linHom PA`, `N.linHom TB`, `N.linHom PB`, `N.linHom TA`.
--
--   The assertion is that the quantity $\dim \mathrm{Hom}_\Delta(N, X/pX) - \dim \mathrm{Hom}_\Delta(N, X[p])$ is unchanged when $X = A$ is replaced by a $\Delta$-stable subgroup of finite index, a dévissage used in the dimension counts attached to Hom-groups of a fixed mod $p$ representation $N$. It is applied in [`Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree`](thm.html#Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree) and, through it, in [`IsLocalRing.finrank_invariants_linHom_units_modPow_eq`](thm.html#IsLocalRing.finrank_invariants_linHom_units_modPow_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex.lean

import Mathlib
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Module

theorem Representation.finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex
    {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ p ∣ Fintype.card Δ)
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) Δ VN)
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a))
    {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA] [FiniteDimensional (ZMod p) WA]
    (TA : Representation (ZMod p) Δ WA)
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0)
    (hιAΔ : ∀ (d : Δ) (w : WA), ιA (TA d w) = act d (ιA w))
    {VB : Type*} [AddCommGroup VB] [Module (ZMod p) VB] [FiniteDimensional (ZMod p) VB]
    (PB : Representation (ZMod p) Δ VB)
    (πB : B →+ VB) (hπB : Function.Surjective πB) (hkerB : ∀ b : B, πB b = 0 ↔ ∃ b' : B, p • b' = b)
    (hπBΔ : ∀ (d : Δ) (b : B), πB ⟨act d b, hB d b b.2⟩ = PB d (πB b))
    {WB : Type*} [AddCommGroup WB] [Module (ZMod p) WB] [FiniteDimensional (ZMod p) WB]
    (TB : Representation (ZMod p) Δ WB)
    (ιB : WB →+ B) (hιB : Function.Injective ιB) (hranB : ∀ b : B, b ∈ Set.range ιB ↔ p • b = 0)
    (hιBΔ : ∀ (d : Δ) (w : WB), (ιB (TB d w) : A) = act d (ιB w)) :
    finrank (ZMod p) (N.linHom PA).invariants + finrank (ZMod p) (N.linHom TB).invariants
      = finrank (ZMod p) (N.linHom PB).invariants + finrank (ZMod p) (N.linHom TA).invariants := by sorry
