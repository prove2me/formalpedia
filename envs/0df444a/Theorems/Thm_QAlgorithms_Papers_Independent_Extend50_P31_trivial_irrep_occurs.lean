-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_trivial_irrep_occurs
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.trivial_irrep_occurs
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T05:23:48.466594+00:00
-- url     : https://prove2.me/theorems/cc84b445-837c-44eb-a0eb-ee8856667bf3
-- title:
--   The trivial irrep occurs in a simply reducible unitary conjugation representation
-- statement:
--   Let $U:G\to U(n)$ be an irreducible unitary representation of a finite group, with $n>0$, and let $U\otimes\overline U$ be isomorphic to a direct sum of exactly one copy of each irreducible representation indexed by a finite set $\Theta$. Then the label of the one-dimensional trivial representation belongs to $\Theta$.
--
--   The conclusion is derived from the explicit intertwining isomorphism, rather than being assumed as part of the decomposition data. It is needed to identify the uniform spectral channel with its trivial central projector.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF p.9 Lemma 10 Eq.(37), specialized to the simply reducible decomposition in Eq.(47), PDF p.11.

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44 QAlgorithms.Papers.Independent.Dependency50.P16
open scoped Matrix ComplexConjugate

theorem QAlgorithms.Papers.Independent.Extend50.P31.trivial_irrep_occurs {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) : D.F.trivial ∈ D.theta := by sorry
