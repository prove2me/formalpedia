-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_proposition_A_6
-- name    : QAlgorithms.Papers.Independent.Support50.P12.proposition_A_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:56:54.592342+00:00
-- url     : https://prove2.me/theorems/e9688167-00a3-4cf4-bd6c-1b075c68828f
-- title:
--   Proposition A.6
-- statement:
--   Let $0<p<1$, $q<0$, $1/p+1/q=1$, and let $A,B$ be arbitrary operators on a nonzero finite-dimensional complex Hilbert space with $\operatorname{supp}|A|\le\operatorname{supp}|B^*|$. Put $|X|=\sqrt{X^*X}$ and $\|X\|_s=(\operatorname{Tr}|X|^s)^{1/s}$ for $X
--   e0$, and $\|0\|_s=0$, including negative $s$.
--
--   Then
--
--   $$\|AB\|_1\ge\|A\|_p\|B\|_q,$$
--
--   with equality exactly when $|A|^p=c|B^*|^q$ for some $c\ge0$. The adjoint stays inside the absolute value, and kernel powers use the paper's support convention. This is the inverse operator Hölder inequality with its full equality case.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 46, Proposition A.6

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Proposition A.6, PDF p.46: inverse Hölder, B* INSIDE the absolute value,
negative q functional, and proportionality with a nonnegative scalar including zero. -/
theorem proposition_A_6 [Nonempty I] (p q : ℝ) (hp : p ∈ Ioo 0 1) (hq : q < 0)
    (hpq : 1 / p + 1 / q = 1) (X Y : Mat I) (hs : Supports (absOp X) (absOp (Yᴴ))) :
    QAlgorithms.traceNorm (X * Y) ≥ signedSchatten p X * signedSchatten q Y ∧
    (QAlgorithms.traceNorm (X * Y) = signedSchatten p X * signedSchatten q Y ↔
      ∃ c : ℝ, 0 ≤ c ∧ supportPower (absOp X) p = (c : ℂ) • supportPower (absOp (Yᴴ)) q) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
