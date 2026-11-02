-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_unbounded_quasipoints_over_infinity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.unbounded_quasipoints_over_infinity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:42:14.852191+00:00
-- url     : https://prove2.me/theorems/a0f707ee-5f15-41d5-a4d9-3e5875879bac
-- title:
--   unbounded-quasipoints-compactification
-- statement:
--   Let $M$ be a noncompact locally compact Hausdorff space and $M_\infty$ its one-point compactification. A quasipoint $\mathfrak B$ has the canonical extension
--
--   $$\widetilde{\mathfrak B}=\{V\in T(M_\infty):V\cap M\in\mathfrak B\}.$$
--
--   This is a quasipoint of $T(M_\infty)$ and lies over $\infty$ exactly when $\mathfrak B$ is unbounded. The extension is defined by restriction along the canonical inclusion of $M$.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 49, unbounded-quasipoints-compactification

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- unbounded-quasipoints-compactification; de Groote, Observables I, PDF p./pp. 49.
-/
theorem unbounded_quasipoints_over_infinity {M : Type u} [TopologicalSpace M] [LocallyCompactSpace M] [T2Space M]
    (hnoncompact : ¬ CompactSpace M) (B : StoneSpectrum (Opens M)) :
    ∃ C : StoneSpectrum (Opens (OnePoint M)), C.val = compactificationBase B ∧
      (LiesOver C OnePoint.infty ↔ IsUnboundedQuasipoint B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
