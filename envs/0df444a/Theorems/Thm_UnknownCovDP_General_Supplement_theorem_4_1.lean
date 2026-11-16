-- Prove2me | Theorems.Thm_UnknownCovDP_General_Supplement_theorem_4_1
-- name    : UnknownCovDP.General.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:03.447189+00:00
-- url     : https://prove2.me/theorems/2cdd9642-cb8f-463f-8b88-82d6a7ba0d23
-- title:
--   Theorem 4.1 — private mean estimation with finite Mahalanobis error is impossible when d ≥ n + 2
-- statement:
--   Under the prior $\mathcal P_{\mathrm{rel}}(d)$, the mean is $\mu\sim N(0,I_d)$ and, independently, $\Sigma=I_d-vv^\top$ with $v$ uniform on the unit sphere of $\mathbb R^d$. Given $(\mu,\Sigma)$, the dataset is $X\sim N(\mu,\Sigma)^{\otimes n}$. For a positive semidefinite $\Sigma$ with pseudo-inverse $\Sigma^\dagger$, the Mahalanobis norm is $d_\Sigma(y)=\sqrt{y^\top\Sigma^\dagger y}$ if $y$ lies in the column space of $\Sigma$, and $d_\Sigma(y)=\infty$ otherwise.
--
--   There is a constant $C>0$ such that for all $d,n\in\mathbb N$ and all $\varepsilon,\delta\ge0$, if $d\ge n+2$ then every $(\varepsilon,\delta)$-differentially private mechanism $\mathcal M$ satisfies
--   $$\Pr_{(\mu,\Sigma)\sim\mathcal P_{\mathrm{rel}},\ X\sim N(\mu,\Sigma)^{\otimes n}}\bigl[d_\Sigma(\mathcal M(X)-\mu)<\infty\bigr]\le n\delta ,$$
--   the probability being also over the coins of $\mathcal M$. (The constant $C$ appears nowhere else in the statement, as printed.)
--
--   So with fewer than $d-1$ samples no private algorithm can estimate the mean with finite error measured relative to the unknown covariance, unless $\delta$ is at least of order $1/n$.
--
--   Differences from the source:
--   - reading: There exists a constant C > 0 (C appears nowhere else) → ∃ C : ℝ, 0 < C ∧ … with C unused; reason: kept as printed; it is vacuous and does not change the conclusion
--   - encoding: Pr over (µ,Σ) ∼ P_rel and X ∼ N(µ,Σ)^{⊗n} → the base experimentProb, which also integrates over the mechanism's coins; reason: the output M(X) is random; the probability of the event is over the coins as well
--   - encoding: d_Σ(M(X) − µ) < ∞ → mahalanobis S (y − μ) < ⊤ with mahalanobis valued in [0, ∞] and Σ† the published LatentRobust.pinv; reason: the paper's definition of d_Σ on p. 27, verbatim
--   - encoding: nδ → ENNReal.ofReal (n * δ); reason: probabilities are in [0, ∞]; n δ ≥ 0 since δ ≥ 0
--   - encoding: (ε, δ)-DP mechanism M → Markov kernel M with PrivRobustStat.IsApproxDP (fun X => M X) ε δ; reason: the base mission's model and published DP definition
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Theorem 4.1, printed p. 27 (PDF p. 28); d_Σ and prior eq. (17), same page

import Mathlib
import Definitions.Def_UnknownCovDP_General_Supplement_RelPrior

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General.Supplement

/-- Theorem 4.1, printed p. 27, PDF p. 28. There is a constant `C > 0` such that for all `d, n ∈ ℕ`
and `ε, δ ≥ 0`, if `d ≥ n + 2` then every `(ε, δ)`-DP mechanism `M` satisfies
`Pr_{(μ,Σ) ∼ P_rel, X ∼ N(μ,Σ)^{⊗n}}[d_Σ(M(X) − μ) < ∞] ≤ nδ` (the probability also over the
mechanism's coins). The constant `C` occurs nowhere else, as printed. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) (ε δ : ℝ), 0 ≤ ε → 0 ≤ δ → n + 2 ≤ d →
      ∀ M : Algorithm d n, IsMarkovKernel M →
        PrivRobustStat.IsApproxDP (fun X => M X) ε δ →
        experimentProb (Prel d) n M (fun μ S _ => {y | mahalanobis S (y - μ) < ⊤}) ≤
          ENNReal.ofReal (n * δ) := by sorry

end UnknownCovDP.General.Supplement
