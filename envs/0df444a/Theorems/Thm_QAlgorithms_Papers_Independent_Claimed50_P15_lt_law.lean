-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_lt_law
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.lt_law
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:49:28.720487+00:00
-- url     : https://prove2.me/theorems/c5fe3384-18df-4c18-a489-f4b3281758cc
-- title:
--   Large-time mean and weak law for TD FCS
-- statement:
--   For finite quantum approximants $Q_m$, assume TD on an open symmetric interval $I\supset[0,1]$, and LT: the finite limits $e(s)=\lim_{t\to\infty}e_t(s)/t$ exist and are differentiable on $I$. Let $P_t$ be the thermodynamic FCS, $\omega_{mt}$ the evolved states, and $\Sigma_m^t$ the finite mean entropy-production observables. With $\Sigma^+=e'(1)$,
--
--   $$\lim_{t\to\infty}\lim_{m\to\infty}\omega_m(\Sigma_m^t)=-\lim_{t\to\infty}\frac1t\lim_{m\to\infty}\operatorname{Ent}(\omega_{mt}|\omega_m)=\lim_{t\to\infty}\mathbb E_{P_t}\phi=\Sigma^+\ge0,\qquad P_t\Rightarrow\delta_{\Sigma^+}.$$
--
--   The inner real limits exist at every positive time. If all approximants are time-reversal invariant, then $\Sigma^+=-e'(0)$ and $\inf_{s\in[0,1]}e(s)=e(1/2)$. Thermodynamic limits precede large-time limits throughout. The factor $1/t$ follows the entropy balance (4.1).
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 26, Large-time mean and weak law for TD FCS

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Large-time mean and weak law, arXiv:1109.3804v2, PDF pp.25--26.
The printed finite-time (4.13) misses a factor t: the defining entropy balance
is (4.1), and all limits below put m before t. No LDP or CLT is inferred here. -/
theorem lt_law (Q : ℕ → FiniteSystem) (I : Set ℝ) (hLT : HasLT Q I) :
    (∀ t : ℝ, 0 < t →
      Tendsto (fun m => evaluate (Q m).omega (meanProduction (Q m).H (Q m).omega t))
        atTop (nhds (tdMeanProduction Q t)) ∧
      Tendsto (fun m => finiteRelativeEntropyNats (evolvedState (Q m).H (Q m).omega t) (Q m).omega)
        atTop (nhds (tdRelativeEntropy Q t))) ∧
    Tendsto (tdMeanProduction Q) atTop (nhds (deriv (ltEntropic Q) 1)) ∧
    Tendsto (fun t : ℝ => -tdRelativeEntropy Q t / t) atTop (nhds (deriv (ltEntropic Q) 1)) ∧
    Tendsto (fun t : ℝ => ∫ phi : ℝ, phi ∂tdFCS Q t) atTop (nhds (deriv (ltEntropic Q) 1)) ∧
    0 ≤ deriv (ltEntropic Q) 1 ∧
    WeakMeasureLimit (tdFCS Q) atTop (Measure.dirac (deriv (ltEntropic Q) 1)) ∧
    ((∀ m, IsFiniteTRI (Q m).H (Q m).omega) →
      deriv (ltEntropic Q) 1 = -deriv (ltEntropic Q) 0 ∧
      sInf (ltEntropic Q '' Set.Icc (0 : ℝ) 1) = ltEntropic Q (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
