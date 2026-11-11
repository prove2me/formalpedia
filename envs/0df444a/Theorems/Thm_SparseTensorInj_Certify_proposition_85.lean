-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_proposition_85
-- name    : SparseTensorInj.Certify.proposition_85
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:38:19.225508+00:00
-- url     : https://prove2.me/theorems/ff2f3af4-94f1-4acf-b528-61fade8acf88
-- title:
--   Proposition 85 ([BBvH23]) — moments of a Gaussian matrix series
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $d\ge1$, $N\ge0$, let $B_1,\dots,B_N\in\mathbb R^{d\times d}$ be deterministic, $g_1,\dots,g_N$ independent standard Gaussians, and $W=\sum_jg_jB_j$ the Gaussian matrix series with parameters $\sigma_G,\nu_G$ (Definition 84). Then for every integer $t\ge1$,
--   $$\Big(\mathbb E\big[\|W\|_{\mathrm{op}}^{2t}\big]\Big)^{1/(2t)}\le C\Big(\sigma_G+\sqrt{\sigma_G\nu_G}\,(\log(2d))^{3/4}+\nu_G\sqrt t\Big).$$
--   It follows from Corollary 2.2 and Lemma 2.5 of Bandeira, Boedihardjo and van Handel [BBvH23] (intrinsic freeness), and is applied conditionally to $G_s$ in Lemma 89.
--
--   Differences from the source:
--
--   - encoding: B_j ∈ ℝ^{d×d} with log(2d) (d ≥ 1 implicit) → 1 ≤ d; reason: a d × d matrix with d = 0 has no entries; log(2d) presupposes d ≥ 1
--   - encoding: ν_G² = ‖Cov(vec(W))‖_op → nuG B = √‖covVec B‖_op with covVec B[(a,b),(c,e)] = Σ_j B_j[a,b] B_j[c,e]; reason: that is the covariance of vec(W) when the g_j are i.i.d. N(0,1)
--   - encoding: (E‖W‖_op^{2t})^{1/(2t)} for independent standard Gaussians g_j → (∫⁻ ofReal(‖W(g)‖_op^{2t}) d(N(0,1)^{⊗N}))^{1/(2t)} compared in [0, ∞] with ofReal of the right-hand side; reason: the product Gaussian measure is the law of g; the lower integral of a non-negative function is its expectation; the right-hand side is non-negative
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 48, Proposition 85 (Definition 84, pp. 47–48; from [BBvH23])

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_GaussianSeries

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Proposition 85 (p. 48, from [BBvH23]): there is a universal `C > 0` such that for every
Gaussian matrix series `W = Σ_{j=1}^N g_j B_j` (`g_j` i.i.d. `N(0, 1)`, `B_j ∈ ℝ^{d × d}`) with
parameters `σ_G, ν_G` (Definition 84) and every integer `t ≥ 1`,
`(E ‖W‖_op^{2t})^{1/(2t)} ≤ C (σ_G + √(σ_G ν_G) (log(2d))^{3/4} + ν_G √t)`. -/
theorem proposition_85 : ∃ C : ℝ, 0 < C ∧
    ∀ (N d : ℕ) (B : Fin N → Matrix (Fin d) (Fin d) ℝ) (t : ℕ), 1 ≤ d → 1 ≤ t →
      (∫⁻ g, ENNReal.ofReal (opNorm (gaussSeries B g) ^ (2 * t))
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)) ^ ((1 : ℝ) / (2 * (t : ℝ))) ≤
        ENNReal.ofReal (C * (sigmaG B + Real.sqrt (sigmaG B * nuG B) *
          Real.log (2 * (d : ℝ)) ^ ((3 : ℝ) / 4) + nuG B * Real.sqrt t)) := by sorry

end SparseTensorInj.Certify
