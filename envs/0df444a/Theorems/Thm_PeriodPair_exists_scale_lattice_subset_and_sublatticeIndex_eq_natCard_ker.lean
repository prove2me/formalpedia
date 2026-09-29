-- Prove2me | Theorems.Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
-- name    : PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/a357185c-bcec-50d9-a623-43e9133224df
-- title:
--   Dual homothety for a homomorphism of lattice curves
-- statement:
--   Let $L$ and $L'$ be period pairs, each given by two $\mathbb{R}$-independent complex periods $\omega_1,\omega_2$ spanning a lattice in $\mathbb{C}$, and assume $g_2(L)^3 - 27\,g_3(L)^2 \neq 0$ and $g_2(L')^3 - 27\,g_3(L')^2 \neq 0$, so that the associated Weierstrass curves $E_L : a_1=a_2=a_3=0$, $a_4 = -g_2(L)/4$, $a_6 = -g_3(L)/4$ and $E_{L'}$ (likewise from $g_2(L'),g_3(L')$) have nonvanishing discriminant and the uniformising maps $\Phi_L,\Phi_{L'}\colon \mathbb{C} \to E(\mathbb{C})$ are defined, sending each lattice point to the zero point and each $z$ outside the lattice to the affine point with coordinates given by the Weierstrass functions of the respective lattice. Let $\alpha$ be a unit of $\mathbb{C}$ and let $\psi\colon E_L(\mathbb{C}) \to E_{L'}(\mathbb{C})$ be a homomorphism of the additive point groups satisfying $\Phi_{L'}(\alpha z) = \psi(\Phi_L(z))$ for every $z \in \mathbb{C}$. Then there exists a unit $\beta$ of $\mathbb{C}$ such that the lattice of the scaled period pair $L'$ with periods $\beta\omega_1(L'), \beta\omega_2(L')$ is contained, as a subset of $\mathbb{C}$, in the lattice of $L$, and the index of that scaled lattice as a subgroup of the lattice of $L$ equals the cardinality of the kernel of $\psi$ (both being $0$ in the infinite case, by the conventions for subgroup index and `Nat.card`).
--
--   This is the dual-isogeny direction of the dictionary between homomorphisms of complex tori and homotheties between lattices: a homomorphism of the point groups lifting $z \mapsto \alpha z$ produces a homothety $\beta\Lambda' \subseteq \Lambda$ whose index matches the degree $\#\ker\psi$. It feeds into [`PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient`](thm.html#PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient), where the quotient is in addition shown to be cyclic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (α : ℂˣ)
    (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
    (hψ : ∀ z : ℂ, L'.toPoint hL' ((α : ℂ) * z) = ψ (L.toPoint hL z)) :
    ∃ β : ℂˣ, ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = Nat.card ψ.ker := by sorry
