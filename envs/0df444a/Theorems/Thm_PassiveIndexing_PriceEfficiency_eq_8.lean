-- Prove2me | Theorems.Thm_PassiveIndexing_PriceEfficiency_eq_8
-- name    : PassiveIndexing.PriceEfficiency.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:58.148461+00:00
-- url     : https://prove2.me/theorems/2f1f1013-e7cb-47b0-b648-e7b6a91ea502
-- title:
--   (8), p. 6223 — covariance matrix of the public statistic
-- statement:
--   For a nonindexer set $NI$ with $1\le |NI|<m$, put $N=|NI|$ and form the public statistic $y$ in (4). Its covariance matrix is
--   $$
--   \operatorname{var}(y)=\Sigma_{yy}(N)=
--   \begin{bmatrix}
--   \Sigma_{vv}+N^{-1}\Sigma_{\varepsilon\varepsilon}&\Sigma_{vv}\mathbf 1\\
--   \mathbf 1'\Sigma_{vv}&m\mathbf 1'\Sigma_{vv}g
--   \end{bmatrix}.
--   $$
--   Only the upper-left block depends on $N$. This covariance matrix is the matrix inverted in the paper's conditional-variance and derivative formulas.
--
--   **Formalization Note** The model hypothesis includes the positive definite matrices, Gaussian laws, independence, and measurability. The section assumes both investor types are present, and the lower bound ensures that $N^{-1}$ denotes the intended reciprocal.
-- source:
--   Baruch & Zhang, The Distortion in Prices Due to Passive Investing, Management Science 68(8), 2022, p. 6223, equation (8); derivation p. 6230; https://doi.org/10.1287/mnsc.2021.4114

import Mathlib
import Definitions.Def_PassiveIndexing_PriceEfficiency_Model

namespace PassiveIndexing.PriceEfficiency

open MeasureTheory ProbabilityTheory Matrix

/-- Equation (8), p. 6223: covariance of the public statistic with itself. -/
theorem eq_8 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (muv : EuclideanSpace ℝ (Fin n))
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (v : Ω → EuclideanSpace ℝ (Fin n))
    (eps : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hmodel : SignalModel P muv Svv See v eps)
    (NI : Finset (Fin m)) (hNI : Admissible NI) :
    ∀ a b : Fin n ⊕ Unit,
      cov[fun ω => yStat Svv See v eps NI ω a,
        fun ω => yStat Svv See v eps NI ω b; P] =
          Syy m Svv See (NI.card : ℝ) a b := by sorry

end PassiveIndexing.PriceEfficiency
