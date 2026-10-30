-- Prove2me | Theorems.Thm_RiskEU_Complete_proposition_4_stochastic_corrected
-- name    : RiskEU.Complete.proposition_4_stochastic_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:03:21.339836+00:00
-- url     : https://prove2.me/theorems/141bb5bc-56c6-45a8-a743-ab6bf8b649eb
-- title:
--   Proposition 4 (corrected: zero-signal intensity limit) — consistency and ordering
-- statement:
--   Let $N\ge2$, $\mu\in\mathbb R^N$, $\Sigma\succ0$, $\gamma>0$, and a fixed finite $\lambda\ge0$ be given. On any probability space let $(r_t)_{t\ge0}$ be mutually independent with common law $\mathcal N(\mu,\Sigma)$. For each integer $T>N+7$, estimate both $\mu$ and $\Sigma$ from the first $T$ observations, centering the covariance by the sample mean and dividing by $T$. Use (9)–(11) to form $\hat w_T(\kappa)$. Let $w^\star=w_g+B\mu/\gamma$, with $w_g$, $B$, $\mu_g$, $\sigma_g^2$ and $\psi^2$ computed from the population market by (3)–(7). Set $E_T(\kappa)=E_P[U(\hat w_T(\kappa))]$, $V_T(\kappa)=\operatorname{Var}_P(U(\hat w_T(\kappa)))$, and $R_T=E_T-\lambda\sqrt{V_T}$, using the true population utility $U(w)=w^\top\mu-(\gamma/2)w^\top\Sigma w$.
--
--   For every such $T$ the sample covariance is almost surely nonsingular. For every $\kappa\in[0,1]$, utility is integrable and square-integrable, and its actual expectation and variance equal the exact formulas (IA2) and (13)–(19), including every coefficient and $C(T,N,\psi^2)$. The market-derived scalar parameters satisfy their standing conditions. The maximum of $R_T$ and minimum of $V_T$ on $[0,1]$ are attained, and
--
--   $$\kappa_E(T)=\frac{(T-N)(T-N-3)}{T(T-2)}\frac{\psi^2}{\psi^2+(N-1)/T}\in[0,1]$$
--
--   maximizes the actual sampling mean. Every variance minimizer $\kappa_V$ and every robust maximizer $\kappa_R$ satisfy
--
--   $$\kappa_V\le\kappa_R\le\kappa_E(T).$$
--
--   Every sequence $\kappa_R(T)$ of robust maximizers at admissible sample sizes, with arbitrary values at the remaining finitely many sizes, satisfies
--
--   $$\psi^2>0\ \Longrightarrow\ \kappa_R(T)\to1,\qquad \psi^2=0\ \Longrightarrow\ \bigl(\kappa_R(T)=0\text{ for every }T>N+7\bigr)\text{ and }\kappa_R(T)\to0.$$
--
--   Throughout the whole domain $\psi^2\ge0$, including the zero case, the actual Gaussian sample-based portfolio is consistent:
--
--   $$\forall\varepsilon>0,\qquad P\!\left(\|\hat w_T(\kappa_R(T))-w^\star\|_2\ge\varepsilon\right)\longrightarrow0.$$
--
--   This is the full stochastic content of Proposition 4. The market, dimension, risk aversion and robustness weight remain fixed as $T$ grows. The theorem concerns oracle intensities computed from true sampling moments; it does not substitute known covariance or feasible estimated intensities. There is no short-selling constraint.
--
--   **Formalization Note** The supporting moment and nonsingularity assertions are conclusions. The paper's unqualified intensity-to-one sentence fails at zero signal, but the portfolio still converges to $w^\star=w_g$. No big-O or unspecified failure probability is used.
--
--   Differences from the source:
--   - correction: κ_R tends to one under Assumptions 1–2 without excluding ψ²=0 → κ_R tends to one if ψ²>0; if ψ²=0 every admissible robust maximizer is zero and every optimizer sequence tends to zero; reason: N=2, μ=0, Σ=I₂, γ=1, λ=0 with iid Gaussian observations gives E_T(κ)=−(T−2)/(4(T−3))−Tκ²/(2(T−3)(T−5)) for all T≥10, uniquely maximized at zero; consistency and ordering retain the full domain
--   - encoding: real N-vectors and iid samples (r₁,…,r_T) as T grows; consistent estimator → Fin N vectors, Euclidean Gaussian returns, and the first T entries of one infinite iid sequence; consistency is convergence in probability in Euclidean norm; reason: canonical finite-dimensional representation and the usual statistical meaning of consistency; changing the starting index changes no sample
--   - encoding: actual finite sampling moments and inverse sample covariance used in (9)–(21), with formulas in Proposition 1 and Proposition IA.1 → sampling integrals and variance, with integrability, L² utility, almost-sure nonzero sample-covariance determinant, the scalar standing conditions, and both formula identities stated as conclusions; reason: makes the source quantities well-defined without using total-function defaults or assuming any proof conclusion
--   - encoding: κ_R solves the maximization (21), κ_V minimizes variance, and κ_E maximizes mean → attainment, interval membership and (IA3) maximality are conclusions; ordering holds for every pair of optimizers and the limits and consistency for every optimizer sequence, with arbitrary inadmissible initial terms; reason: explicit argmax and argmin semantics avoid empty optimizer quantifiers or a favorable tie-breaking selection
-- source:
--   Lassance, Martín-Utrera, and Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546, version dated August 18, 2023, Proposition 4, p. 20 (PDF p. 20); proof pp. IA44–IA45 (PDF pp. 91–92); (13)–(19), pp. 14–15, and (IA1)–(IA3), p. IA1 (PDF p. 48)

import Mathlib
import Definitions.Def_RiskEU_Complete_StochasticModel

namespace RiskEU.Complete

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

/-- Proposition 4, p. 20, SSRN 3855546 (August 18, 2023), full stochastic version.
The printed intensity-to-one assertion is false when psi2 = 0: N=2, mu=0,
Sigma=I, gamma=1, lam=0 gives the unique maximizer 0 for every T >= 10.
Only that assertion is corrected; portfolio consistency retains the entire domain. -/
theorem proposition_4_stochastic_corrected {N : ℕ} (M : Market N)
    (hN : 2 ≤ N) (hSigma : M.Sigma.PosDef) (hgamma : 0 < M.gamma)
    (lam : ℝ) (hlam : 0 ≤ lam)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (hr : IsGaussianSequence M P r) :
    (scalarParams M lam).Standing ∧
    (∀ T : ℕ, N + 7 < T →
      (∀ᵐ ω ∂P, (sampleCov (sampleData (prefixReturns r T) ω)).det ≠ 0) ∧
      (∀ kappa ∈ Set.Icc (0 : ℝ) 1,
        Integrable (samplingUtility M r T kappa) P ∧
        MemLp (samplingUtility M r T kappa) 2 P ∧
        samplingMean M P r T kappa = (scalarParams M lam).oosuMean T kappa ∧
        samplingVariance M P r T kappa = (scalarParams M lam).oosuVar T kappa) ∧
      (∃ kappaR : ℝ, IsRobustMaximizer M P r lam T kappaR) ∧
      (∃ kappaV : ℝ, IsVarianceMinimizer M P r T kappaV) ∧
      ((scalarParams M lam).kappaE T ∈ Set.Icc (0 : ℝ) 1 ∧
        IsMaxOn (samplingMean M P r T) (Set.Icc (0 : ℝ) 1)
          ((scalarParams M lam).kappaE T)) ∧
      (∀ kappaV kappaR : ℝ,
        IsVarianceMinimizer M P r T kappaV → IsRobustMaximizer M P r lam T kappaR →
        kappaV ≤ kappaR ∧ kappaR ≤ (scalarParams M lam).kappaE T) ∧
      (M.psi2 = 0 → ∀ kappaR : ℝ, IsRobustMaximizer M P r lam T kappaR → kappaR = 0)) ∧
    (∀ kappaR : ℕ → ℝ,
      (∀ T : ℕ, N + 7 < T → IsRobustMaximizer M P r lam T (kappaR T)) →
      (0 < M.psi2 → Filter.Tendsto kappaR Filter.atTop (nhds 1)) ∧
      (M.psi2 = 0 → Filter.Tendsto kappaR Filter.atTop (nhds 0)) ∧
      PortfolioConsistent M P r kappaR) := by sorry

end RiskEU.Complete
