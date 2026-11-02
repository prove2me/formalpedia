-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P91_schattenThreeLines
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P91.schattenThreeLines
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:22:42.752463+00:00
-- url     : https://prove2.me/theorems/cece3db2-932a-4ffb-84f2-f84ec69e7661
-- title:
--   Schatten three-lines interpolation with arbitrary endpoint exponents
-- statement:
--   Let $d\ge1$ and $S=\{z\in\mathbb C:0\le\operatorname{Re}z\le1\}$. Let $G:S\to M_d(\mathbb C)$ be bounded, holomorphic in the interior, and continuous up to the boundary. Choose $0<\theta<1$ and arbitrary $p_0,p_1\in[1,\infty]$, with no ordering requirement. Define
--   $1/p_\theta=(1-\theta)/p_0+\theta/p_1$, using $1/\infty=0$, and set
--   $M_k=\sup_{t\in\mathbb R}\|G(k+it)\|_{p_k}$ for $k=0,1$. Finite Schatten norms are unnormalized and the norm at infinity is the spectral operator norm. Then
--
--   $$
--   \|G(\theta)\|_{p_\theta}\le M_0^{1-\theta}M_1^\theta.
--   $$
--
--   Both suprema are over nonempty bounded sets. This is the finite matrix version of the recalled three-lines result, following the entrywise convention of the source's footnote 2.
--
--   **Formalization Note** The Lean map is defined on all complex numbers, with hypotheses and evaluations restricted to the strip. Interior holomorphy and continuity up to its boundary are expressed by continuity on the closed strip; no constraint is imposed outside it.
-- source:
--   Monotonicity of $p$-norms of multiple operators via unitary swivels, arXiv:1610.01262v1, PDF p. 4, Lemma 4, Eqs.(25)–(27), footnote 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P91

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakethird100.P91

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (extendedLog upperLogIntegral betaDensity betaZero interpolationExponent)

open QAlgorithms.Papers.Independent.Bridge50.P29
  (positiveComplexPower orderedProduct)

/-- Lemma 4, Eqs.(25)--(27), arXiv:1610.01262v1, PDF p.4.
Finite matrix interpretation follows footnote 2. G is arbitrary outside
the closed strip. The computed endpoint suprema are nonempty and finite
by strip boundedness and finite dimension. No order between p0 and p1 is
assumed; either or both may be infinity, including equal endpoints. -/
theorem schattenThreeLines
    (d : ℕ) (hd : 0 < d) (G : ℂ → Matrix (Fin d) (Fin d) ℂ)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (theta : ℝ) (htheta : 0 < theta ∧ theta < 1)
    (p0 p1 : ℝ≥0∞) (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1) :
    schattenNorm (interpolationExponent theta p0 p1) (G (theta : ℂ)) ≤
      (boundarySup G p0 0) ^ (1 - theta) * (boundarySup G p1 1) ^ theta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P91

end
