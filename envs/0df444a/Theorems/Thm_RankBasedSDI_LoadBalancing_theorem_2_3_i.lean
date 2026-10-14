-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_theorem_2_3_i
-- name    : RankBasedSDI.LoadBalancing.theorem_2_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:25.741482+00:00
-- url     : https://prove2.me/theorems/b8e11dee-27fd-406d-a18c-00e57300370d
-- title:
--   Theorem 2.3(i): under (IC₀), $(\hat X^n,\hat L^n)\Rightarrow(X,L)$, a weak solution of (SDER) and (SDIR) with data (2.17)
-- statement:
--   Consider the sequence of load-balancing systems of §2.1 under its standing assumptions:
--
--   - the routing vector is nonincreasing (2.4);
--   - the service times, initial condition and independence are as on pp. 4–5;
--   - the scaling and critical-load conditions (2.9)–(2.13) hold.
--
--   Define the data
--
--   $$
--   b_r=\lambda_0p_r,\quad r\in[N],\qquad m_i=\hat\lambda_i-\hat\mu_i,\qquad \sigma_i=(\lambda_i+\mu_i(\sigma^{ser}_i)^2)^{1/2},\quad i\in[N].\qquad(2.17)
--   $$
--
--   Assume (IC₀): $\hat X^n(0-)\Rightarrow X_0$, where $X_0$ has law $\mu_0$. Then there exist a stochastic basis $(\Omega',\mathcal F',\mathbb F,P')$ and processes $(X,L,B)$ on it with the following properties:
--
--   1. $(X,L,B)$ is a weak solution of (SDER) with data (2.17), and, with the rank-based drift $\beta(t)=(b_{\mathcal R_i(t)})_i$, also a weak solution of (SDIR);
--   2. $X(0)$ has law $\mu_0$;
--   3. as $n\to\infty$,
--
--   $$
--   (\hat X^n,\hat L^n)\Rightarrow(X,L)\quad\text{in }D(\mathbb R_+,\mathbb R^N)\times C(\mathbb R_+,\mathbb R^N).
--   $$
--
--   The diffusion-scaled queue lengths and cumulative idle times of the load-balancing model thus converge to a reflected rank-based diffusion in the nonnegative orthant. Routing appears in the limit only through the rank-based drift $b=\lambda_0p$.
--
--   **Formalization Note** The following conventions are fixed.
--
--   - The paper speaks of "the solution". The statement takes the existence form: it asserts a weak solution with initial law $\mu_0$ to which the whole sequence converges. Uniqueness in law follows from Proposition 3.1 only through Remark 2.1 (Yamada–Watanabe/Kurtz), which the paper cites and does not prove.
--   - Both (SDER) and (SDIR) are asserted.
--   - Weak convergence to a continuous limit is the referenced `CouplingConverges` on the $2N$-dimensional process `Fin.append X̂ⁿ L̂ⁿ`; it is equivalent to $J_1$ weak convergence.
--   - The limit lives on some $\Omega'$ in universe 0.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 8, Theorem 2.3(i) with (2.17); standing assumptions §2.1–2.2, pp. 3–6

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
import Definitions.Def_RankBasedSDI_LoadBalancing_PoissonProcess
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_RankBasedSDI_LoadBalancing_RankBasedEquations
import Definitions.Def_RankBasedSDI_LoadBalancing_Model
import Definitions.Def_RankBasedSDI_LoadBalancing_ScaledProcesses
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy

namespace RankBasedSDI.LoadBalancing

theorem theorem_2_3_i {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (S : LoadBalancingSequence Ω N) (H : HeavyTraffic S) (μ₀ : ProbabilityMeasure (Fin N → ℝ))
    (hIC : IC0 S μ₀) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (F : Filtration ℝ≥0 mΩ')
      (X L B : Ω' → ℝ → Fin N → ℝ),
      IsWeakSolutionSDER (driftB H) (driftM H) (diffSigma H) P' F X L B ∧
      IsWeakSolutionSDIR (driftB H) (driftM H) (diffSigma H) P' F X L B
        (fun ω t => rankDrift (driftB H) (X ω t)) ∧
      HasLaw (fun ω => X ω 0) (μ₀ : Measure (Fin N → ℝ)) P' ∧
      CouplingConverges S.P P'
        (fun n ω t => Fin.append (Xhat S n ω t) (Lhat S n ω t))
        (fun ω t => Fin.append (X ω t) (L ω t)) := by sorry

end RankBasedSDI.LoadBalancing
