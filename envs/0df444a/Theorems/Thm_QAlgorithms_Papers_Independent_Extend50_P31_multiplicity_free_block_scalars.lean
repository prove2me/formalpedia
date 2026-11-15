-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_multiplicity_free_block_scalars
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.multiplicity_free_block_scalars
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T06:17:23.264039+00:00
-- url     : https://prove2.me/theorems/3f6848c5-e408-4dae-a68a-c3c2703ccac6
-- title:
--   Every intertwiner on a multiplicity-free sum is scalar on each irreducible block
-- statement:
--   Let $G$ be finite and $(\varphi^a)_{a\in A}$ a family of pairwise inequivalent irreducible unitary complex representations. Fix a finite subset $\Theta\subseteq A$. Let $M$ be a complex-linear endomorphism of the direct sum of the coordinate spaces $\mathbb C^{d_a}$ for $a\in\Theta$, intertwining their block-diagonal group action. Then there are complex scalars $(l_a)_{a\in\Theta}$ such that
--
--   $$(Mv)_a=l_a v_a\qquad\text{for every vector }v\text{ and label }a\in\Theta.$$
--
--   The label set $A$ itself need not be finite. This is the multiplicity-free form of Schur's lemma underlying the commutant and spectral description of irreducibly covariant quantum channels.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF pp.9–12, multiplicities Eq.(34), simply reducible decomposition Eq.(47), Proposition 13 commutant formula Eq.(48), and the spectral form Eq.(53).

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31

theorem QAlgorithms.Papers.Independent.Extend50.P31.multiplicity_free_block_scalars {G A : Type*} [Group G] [Fintype G] [DecidableEq A] (F : IrrepFamily G A) (theta : Finset A)
    (M : ((a : {a // a ∈ theta}) → Fin (F.dim a.val) → ℂ) →ₗ[ℂ]
      ((a : {a // a ∈ theta}) → Fin (F.dim a.val) → ℂ))
    (hM : ∀ g v a, M (fun b => ((F.irrep b.val).rho g).mulVec (v b)) a =
      ((F.irrep a.val).rho g).mulVec (M v a)) :
    ∃ l : {a // a ∈ theta} → ℂ, ∀ v a, M v a = l a • v a := by sorry
