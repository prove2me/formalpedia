-- Prove2me | Theorems.Thm_PassiveIndexing_PriceEfficiency_eq_7
-- name    : PassiveIndexing.PriceEfficiency.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:54.438445+00:00
-- url     : https://prove2.me/theorems/9e93b1e0-82d4-485a-817c-c1fe66031b69
-- title:
--   (7), p. 6223 — covariance of payoffs and the public statistic
-- statement:
--   In the Gaussian signal economy, let $NI$ be a set of nonindexers with both investor types present, $1\le |NI|<m$ and let $y$ be the public statistic in (4). The cross-covariance of the payoff vector $v$ and $y$ is
--   $$
--   \operatorname{cov}(v,y)=\Sigma_{vy}=
--   \begin{bmatrix}\Sigma_{vv}&m\Sigma_{vv}g\end{bmatrix}.
--   $$
--   Thus this cross-covariance is independent of the composition and size of $NI$. It supplies the cross term in the Gaussian conditional-variance formula.
--
--   **Formalization Note** The Gaussian laws, mutual independence, positive definite covariance matrices, and measurability are bundled in the signal-model hypothesis. The section assumes both investor types are present, so $1\le |NI|<m$; the lower bound also makes $1/|NI|$ meaningful.
-- source:
--   Baruch & Zhang, The Distortion in Prices Due to Passive Investing, Management Science 68(8), 2022, p. 6223, equation (7); derivation p. 6230; https://doi.org/10.1287/mnsc.2021.4114

import Mathlib
import Definitions.Def_PassiveIndexing_PriceEfficiency_Model

namespace PassiveIndexing.PriceEfficiency

open MeasureTheory ProbabilityTheory Matrix

/-- Equation (7), p. 6223: the payoff-public-statistic covariance is independent of the
indexer partition. The Gaussian signal and independence assumptions are those of §2. -/
theorem eq_7 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (muv : EuclideanSpace ℝ (Fin n))
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (v : Ω → EuclideanSpace ℝ (Fin n))
    (eps : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hmodel : SignalModel P muv Svv See v eps)
    (NI : Finset (Fin m)) (hNI : Admissible NI) :
    ∀ i : Fin n, ∀ a : Fin n ⊕ Unit,
      cov[fun ω => v ω i, fun ω => yStat Svv See v eps NI ω a; P] =
        Svy m Svv See i a := by sorry

end PassiveIndexing.PriceEfficiency
