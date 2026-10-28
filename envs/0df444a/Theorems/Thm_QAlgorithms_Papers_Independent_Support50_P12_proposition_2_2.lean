-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_proposition_2_2
-- name    : QAlgorithms.Papers.Independent.Support50.P12.proposition_2_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:10:11.787953+00:00
-- url     : https://prove2.me/theorems/1357ab5f-d9dc-421b-8dc6-f4957006cfb1
-- title:
--   Proposition 2.2
-- statement:
--   Let $A,B$ be positive semidefinite operators on a nonzero finite-dimensional complex Hilbert space. Let $f:[0,\infty)\to\mathbb R$ be continuous on $(0,\infty)$ with signed extended recession slope $\omega(f)=\lim_{x\to\infty}f(x)/x$. Write $S_f$ for the paper's quantum divergence, $Q_f(A,B)=\langle B^{1/2},f(L_AR_{B^{-1}})B^{1/2}\rangle_{\rm HS}$, and $X^0$ for the support projection. All powers vanish on the kernel, including exponent zero. Traces are representation traces.
--
--   The regularization limit exists and satisfies
--
--   $$\lim_{\varepsilon\downarrow0}S_f(A\Vert B+\varepsilon I)=Q_f(A,B)+\omega(f)\operatorname{Tr}A(I-B^0).$$
--
--   If $A^0\le B^0$, this limit is $Q_f(A,B)$. This makes the supported definition consistent with regularization.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 5, Proposition 2.2

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

/-- Proposition 2.2, PDF p.5: regularization limit and supported-pair consistency. -/
theorem proposition_2_2 [Nonempty I] (f : ℝ → ℝ) (hf : DivergenceGenerator f)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun e : ℝ => div f A (B + (e : ℂ) • 1)) (𝓝[>] 0)
      (𝓝 ((quasi f A B : EReal) + recessionSlope f * (tr (A * (1 - supp B)) : EReal))) ∧
    (Supports A B → Tendsto (fun e : ℝ => div f A (B + (e : ℂ) • 1))
      (𝓝[>] 0) (𝓝 (quasi f A B : EReal))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
