-- Prove2me | Theorems.Thm_RiskEU_RobustShrink_proposition_4
-- name    : RiskEU.RobustShrink.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:07.228875+00:00
-- url     : https://prove2.me/theorems/6f622f55-e252-4386-9222-e2a148097f3e
-- title:
--   Proposition 4, p. 20 — location and limit of robust shrinkage intensity
-- statement:
--   Fix $N\geq2$, $\gamma>0$, $\sigma_g^2>0$, $\psi^2\geq0$, a GMV mean $\mu_g$, and a robustness weight $\lambda\geq0$. For every $T>N+7$, let $V_T(\kappa)$ and $E_T(\kappa)$ be the closed-form OOSU variance and mean, and maximize
--   $$
--   R_T(\kappa)=E_T(\kappa)-\lambda\sqrt{V_T(\kappa)}
--   $$
--   over $\kappa\in[0,1]$. Both this maximum and the minimum of $V_T$ on $[0,1]$ are attained. Every robust maximizer $\kappa_R$ and every variance minimizer $\kappa_V$ satisfy
--   $$
--   \kappa_V\leq\kappa_R\leq\kappa_E(T),
--   $$
--   where $\kappa_E(T)$ is the mean-maximizing intensity (IA3). If $\psi^2>0$, then every sequence choosing a robust maximizer for each $T>N+7$ tends to $1$ as $T\to\infty$.
--
--   The ordering locates the robust portfolio between the least-risk and greatest-mean shrinkage choices.
--
--   **Formalization Note** The additional $\psi^2>0$ condition is necessary only for the limit; at $\psi^2=0$ the claimed limit fails. The consistency of the underlying random portfolio estimator is not posed in this closed-form setting. The OOSU mean and variance are formulas from Proposition IA.1 and Proposition 1, and their identification as moments requires those separate probabilistic results.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Proposition 4, p. 20; Section IA.10, proof of Proposition 4, pp. IA44–IA45

import Mathlib
import Definitions.Def_RiskEU_RobustShrink_Setting

namespace RiskEU.RobustShrink

/-- Proposition 4, p. 20, for the closed-form moments (13)–(19) and (IA1)–(IA3). -/
theorem proposition_4 (p : Params) (hp : p.Standing) :
    (∀ T : ℕ, p.N + 7 < T →
      (∃ kappa ∈ Set.Icc (0 : ℝ) 1,
        IsMaxOn (p.meanRisk T) (Set.Icc (0 : ℝ) 1) kappa) ∧
      (∃ kappa ∈ Set.Icc (0 : ℝ) 1,
        IsMinOn (p.oosuVar T) (Set.Icc (0 : ℝ) 1) kappa)) ∧
    (0 < p.psi2 → ∀ kappaR : ℕ → ℝ,
      (∀ T : ℕ, p.N + 7 < T →
        kappaR T ∈ Set.Icc (0 : ℝ) 1 ∧
        IsMaxOn (p.meanRisk T) (Set.Icc (0 : ℝ) 1) (kappaR T)) →
      Filter.Tendsto kappaR Filter.atTop (nhds 1)) ∧
    (∀ T : ℕ, p.N + 7 < T → ∀ kappaV kappaR : ℝ,
      kappaV ∈ Set.Icc (0 : ℝ) 1 →
      IsMinOn (p.oosuVar T) (Set.Icc (0 : ℝ) 1) kappaV →
      kappaR ∈ Set.Icc (0 : ℝ) 1 →
      IsMaxOn (p.meanRisk T) (Set.Icc (0 : ℝ) 1) kappaR →
      kappaV ≤ kappaR ∧ kappaR ≤ p.kappaE T) := by sorry

end RiskEU.RobustShrink
