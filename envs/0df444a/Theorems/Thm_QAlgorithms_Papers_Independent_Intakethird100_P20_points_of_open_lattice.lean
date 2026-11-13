-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_points_of_open_lattice
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.points_of_open_lattice
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:34:25.631292+00:00
-- url     : https://prove2.me/theorems/68e9de62-e23c-440a-b768-45dd5abd35b1
-- title:
--   Proposition 3.2
-- statement:
--   Let $M$ be a regular Hausdorff space and let $p$ be a nonempty subset of its open-set lattice. Then $p$ is a lattice point, preserving arbitrary joins, if and only if
--
--   $$p=\{U\subseteq M:U\text{ open and }x\in U\}$$
--
--   for a unique $x\in M$. Hausdorff separation makes explicit the source's regular-space convention.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 37, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.2; de Groote, Observables I, PDF p./pp. 37.
-/
theorem points_of_open_lattice {M : Type u} [TopologicalSpace M] [RegularSpace M] [T2Space M]
    (p : Set (Opens M)) (hne : p.Nonempty) :
    IsLatticePoint p ↔ ∃! x : M, p = {U : Opens M | x ∈ (U : Set M)} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
