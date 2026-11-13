-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_compact_space_canonical_point_quotient
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.compact_space_canonical_point_quotient
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:44:54.347552+00:00
-- url     : https://prove2.me/theorems/d537c2d3-344c-43b0-b790-fdbd813d9c5f
-- title:
--   Corollary 3.5
-- statement:
--   For a compact Hausdorff space $M$, each quasipoint of $T(M)$ lies over a unique point, defining a canonical continuous surjection $\operatorname{pt}:Q(T(M))\to M$ with
--
--   $$\bigcap_{U\in\mathfrak B}\overline U=\{\operatorname{pt}(\mathfrak B)\}.$$
--
--   This map is a quotient map: its induced quotient topology is the given topology on $M$. The empty space is allowed.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 56, Corollary 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Corollary 3.5; de Groote, Observables I, PDF p./pp. 56.
-/
theorem compact_space_canonical_point_quotient {M : Type u} [TopologicalSpace M] [CompactSpace M] [T2Space M] :
    ∃ pt : StoneSpectrum (Opens M) → M,
      (∀ B, LiesOver B (pt B)) ∧ Function.Surjective pt ∧
        Continuous pt ∧ Topology.IsQuotientMap pt := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
