-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_irreducible_twirl
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.irreducible_twirl
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T05:21:36.033748+00:00
-- url     : https://prove2.me/theorems/2b954ef6-14f2-47e3-b172-378771e00d99
-- title:
--   Irreducible unitary group averaging is the completely depolarizing channel
-- statement:
--   Let $G$ be finite and $U:G\to U(n)$ an irreducible unitary complex representation with $n>0$. For every matrix $X\in M_n(\mathbb C)$,
--
--   $$\frac1{|G|}\sum_{g\in G}U(g)XU(g)^\dagger=\frac{\operatorname{Tr}X}{n}I_n.$$
--
--   Thus uniform finite-group twirling erases all non-scalar components. The assertion concerns all complex matrices, with no positivity or Hermiticity restriction, and uses the normalized group average and ordinary unnormalized trace.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF pp.12–14, trivial central projector in Eqs.(56),(62) and Proposition 25; Example 55 Eq.(122), PDF p.24.

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44

theorem QAlgorithms.Papers.Independent.Extend50.P31.irreducible_twirl {G : Type*} [Group G] [Fintype G] {n : ℕ} (U : UnitaryIrrep G n) (X : Mat n) :
    (Fintype.card G : ℂ)⁻¹ • (∑ g : G, conjugationMap U g X) =
      (Matrix.trace X / n) • (1 : Mat n) := by sorry
