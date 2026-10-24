-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_proposition_A_4
-- name    : QAlgorithms.Papers.Independent.Support50.P12.proposition_A_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:55:16.159989+00:00
-- url     : https://prove2.me/theorems/8487b3d1-a443-45f1-b2cf-836cd8e9a206
-- title:
--   Proposition A.4
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   Assume $B
--   e0$ and $f$ is convex on $[0,\infty)$. Let $E_B(X)=\sum_bQ_bXQ_b$ be the spectral pinching. Then
--
--   $$S_f(A\Vert B)\ge S_f(E_B(A)\Vert E_B(B))=S_f(E_B(A)\Vert B)\ge(\operatorname{Tr}B)f\!\left(\frac{\operatorname{Tr}A}{\operatorname{Tr}B}\right).$$
--
--   If $A^0\le B^0$ and $f$ is strictly convex, equality in the first inequality is equivalent to $AB=BA$; equality in the second is equivalent to $E_B(A)$ being a nonnegative multiple of $B$; equality between the extreme terms is equivalent to $A$ being a nonnegative multiple of $B$. Both additional hypotheses govern every equality characterization.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 44, Proposition A.4

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

/-- Proposition A.4, PDF pp.44–45: all inequalities, the pinching identity,
and ALL equality characterizations, each retaining strict convexity and support inclusion. -/
theorem proposition_A_4 [Nonempty I] (X Y : Mat I) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hn : Y ≠ 0) (f : ℝ → ℝ) (hf : DivergenceGenerator f) (hc : ConvexOn ℝ (Ici 0) f) :
    div f (pinch Y X) (pinch Y Y) ≤ div f X Y ∧
    div f (pinch Y X) (pinch Y Y) = div f (pinch Y X) Y ∧
    ((tr Y * f (tr X / tr Y) : ℝ) : EReal) ≤ div f (pinch Y X) Y ∧
    (Supports X Y → StrictConvexOn ℝ (Ici 0) f →
      (div f X Y = div f (pinch Y X) Y ↔ Commute X Y) ∧
      (div f (pinch Y X) Y = ((tr Y * f (tr X / tr Y) : ℝ) : EReal) ↔
        ∃ c : ℝ, 0 ≤ c ∧ pinch Y X = (c : ℂ) • Y) ∧
      (div f X Y = ((tr Y * f (tr X / tr Y) : ℝ) : EReal) ↔
        ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • Y)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
