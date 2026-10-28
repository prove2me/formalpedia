-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_touching_interval_sets
-- name    : QAlgorithms.Papers.Independent.Support50.P44.touching_interval_sets
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-24T00:05:42.975352+00:00
-- url     : https://prove2.me/theorems/821cb4f2-b0b9-4cf7-9011-6cdfbbbcafe0
-- title:
--   Touching sets covering an interval
-- statement:
--   Let $K_0,K_1\subseteq\mathbb R$ satisfy $K_0\cup K_1=[0,1]$, $0\in K_0$, and $1\in K_1$. For every $\delta>0$,
--
--   $$\exists u\in K_0\ \exists v\in K_1:\quad 0\le v-u\le\delta.$$
--
--   Neither closedness, disjointness nor measurability is assumed. In particular $u=v$ is permitted at an intersection; this supplies nearby parameters from the two covering sets.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 26, Lemma D.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A B C E G : Type*}

/-- PDF p.26, Lemma D.1: arbitrary covering sets, without closedness,
disjointness or measurability. An intersection permits u = v. -/
theorem touching_interval_sets (K0 K1 : Set ℝ) (hcover : K0 ∪ K1 = Set.Icc 0 1)
    (hzero : 0 ∈ K0) (hone : 1 ∈ K1) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ u ∈ K0, ∃ v ∈ K1, 0 ≤ v - u ∧ v - u ≤ delta := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
