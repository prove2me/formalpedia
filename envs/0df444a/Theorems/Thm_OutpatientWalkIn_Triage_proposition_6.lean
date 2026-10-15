-- Prove2me | Theorems.Thm_OutpatientWalkIn_Triage_proposition_6
-- name    : OutpatientWalkIn.Triage.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:09.660922+00:00
-- url     : https://prove2.me/theorems/8bc7e9ef-ca3d-4068-b833-31832ca68587
-- title:
--   Proposition 6, pp. 27–28 — the triage model costs less if C_L/C_O ≤ α̲, the strategic model costs less if C_L/C_O ≥ ᾱ
-- statement:
--   Consider the observable setting under the standing assumptions, with $C_O>0$ and $\lambda_E>0$. Let $\underline\mu_W>0$ satisfy (15), $R-C_W\,w(\lambda_E/\underline\mu_W)=0$, and suppose $\mu>\underline\mu_W$. Suppose $o$ is differentiable at $\lambda_E/\mu$ and at $\lambda_E/\underline\mu_W$, and define
--   $$\underline\alpha=\frac{o'(\lambda_E/\mu)}{\mu},\qquad \overline\alpha=\frac{o'(\lambda_E/\underline\mu_W)}{\underline\mu_W}\cdot\max\Big\{\frac{\lambda_E}{\lambda\,\pi(R/C_D,\mu-\underline\mu_W)},1\Big\}.$$
--   Write $Z^s(\mu_S;\delta,p_W,p_B)$ for the strategic model's cost (Ob.P) and $Z^t(\mu_S)$ for the triage model's cost (T.Ob.P). Then:
--
--   1. If $C_L/C_O\le\underline\alpha$, the triage model costs less: for every allocation $\mu_S\in[0,\mu)$ and every observable equilibrium $(\delta,p_W,p_B)$ at $\mu_S$ there is an allocation $\mu'_S\in[0,\mu)$ with
--   $$Z^t(\mu'_S)\le Z^s(\mu_S;\delta,p_W,p_B).$$
--   2. If $C_L/C_O\ge\overline\alpha$, the strategic model costs less: for every allocation $\mu_S\in[0,\mu)$ there is an allocation $\mu'_S\in[0,\mu)$ at which an observable equilibrium exists and every observable equilibrium $(\delta,p_W,p_B)$ satisfies
--   $$Z^s(\mu'_S;\delta,p_W,p_B)\le Z^t(\mu_S).$$
--
--   The result answers when a clinic should close its walk-in hours to patients who could book: when lost demand is cheap relative to overtime, triage wins; when it is expensive, letting patients choose freely wins.
--
--   **Formalization Note** "Costs less" means "costs no more" (p. 26). The comparison of optimal costs is stated in ∀–∃ form, so that it does not presuppose that the minimization problems (Ob.P) and (T.Ob.P) attain their minima; the strategic side quantifies over every equilibrium at the chosen allocation. Added hypotheses: $C_O>0$ (so that $C_L/C_O$ is the paper's ratio rather than Lean's $C_L/0=0$); $\lambda_E>0$ and $\underline\mu_W$ given by (15) (the paper presupposes $\underline\mu_W$); differentiability of $o$ at the two points where $\underline\alpha$ and $\overline\alpha$ evaluate $o'$ (Assumption 2 gives only convexity and monotonicity); allocations $\mu_S\in[0,\mu)$ on both sides, since $\mu_S=\mu$ leaves no walk-in hours for the exogenous walk-ins.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), pp. 27–28, Proposition 6, with α̲, ᾱ and (T.Ob.P) on p. 27; proof in Online Appendix pp. 35–37

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace OutpatientWalkIn.Triage

theorem proposition_6 (M : Model) (hM : M.Standing) (hCO : 0 < M.CO) (hlamE : 0 < M.lamE)
    (μWl : ℝ) (hμWl : 0 < μWl) (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) (hμ : μWl < M.mu)
    (ho₁ : DifferentiableAt ℝ M.o (M.lamE / M.mu))
    (ho₂ : DifferentiableAt ℝ M.o (M.lamE / μWl)) :
    (M.CL / M.CO ≤ M.alphaLow →
      ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e →
        ∃ μS' ∈ Set.Ico 0 M.mu, M.triageCost μS' ≤ M.obsCost μS e) ∧
    (M.alphaHigh μWl ≤ M.CL / M.CO →
      ∀ μS ∈ Set.Ico 0 M.mu, ∃ μS' ∈ Set.Ico 0 M.mu, (∃ e : ObsStrategy, M.IsObsEq μS' e) ∧
        ∀ e : ObsStrategy, M.IsObsEq μS' e → M.obsCost μS' e ≤ M.triageCost μS) := by sorry

end OutpatientWalkIn.Triage
