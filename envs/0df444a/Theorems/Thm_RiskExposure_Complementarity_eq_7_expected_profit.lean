-- Prove2me | Theorems.Thm_RiskExposure_Complementarity_eq_7_expected_profit
-- name    : RiskExposure.Complementarity.eq_7_expected_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:52.491006+00:00
-- url     : https://prove2.me/theorems/4bad5ebe-960e-4546-87b6-251c4a0e3994
-- title:
--   (7), p. 9 — E[Π_i] = P(Z_i)(Z_i − v_i) − P(Z_i)·D_i(Z_{−i}) + (1 − P(Z_i))·(expected payoff after failure)
-- statement:
--   In the setting of the mission, with the success probability $P$ satisfying $P(z)\in(0,1)$ and Assumption 1 on $[\underline Z,\overline Z]$, let $Z\in[\underline Z,\overline Z]^N$ and let $i$ be a bank. Then bank $i$'s expected profit decomposes as
--   $$\mathbb E[\Pi_i(\omega;Z)]=P(Z_i)(Z_i-v_i)-P(Z_i)\,\mathcal D_i(Z_{-i})+\big(1-P(Z_i)\big)\sum_{\omega_{-i}}\Big[0-v_i-\Big(d_i^*(\omega^{i=f})-\sum_j\theta_{ij}d_j^*(\omega^{i=f})\Big)\Big]^+\Pr(\omega_{-i}),$$
--   where $\mathcal D_i$ is the cross-subsidy (5) and $\Pr(\omega_{-i})=\prod_{j\ne i}\Pr(\omega_j)$.
--
--   The first two terms are the payoff upon success, reduced by the expected net payment $\mathcal D_i$ to the other banks; the last term is the payoff upon failure, which can be positive only in non-regular networks. Equation (6) is the special case where that last term vanishes.
--
--   **Formalization Note** The sum over $\omega_{-i}$ is a sum over the states $\omega$ with $\omega_i=f$, weighted by the product over $j\ne i$. Assumption 1 is carried as standing hypotheses although the identity does not use it.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), p. 9, equation (7)

import Mathlib
import Definitions.Def_RiskExposure_Complementarity_Model

namespace RiskExposure.Complementarity

theorem eq_7_expected_profit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi) (i : ι) :
    expProfit dbar v P Z i =
      P (Z i) * (Z i - v i) - P (Z i) * distortion dbar v P Z i
        + (1 - P (Z i)) *
          ∑ ω ∈ Finset.univ.filter (fun ω : ι → Bool => ω i = false),
            max (0 - v i - (paymentEq dbar v ω Z i - ∑ j, theta dbar i j * paymentEq dbar v ω Z j)) 0
              * ∏ j ∈ Finset.univ.erase i, (if ω j then P (Z j) else 1 - P (Z j)) := by sorry

end RiskExposure.Complementarity
