-- Prove2me | Theorems.Thm_RiskExposure_Complementarity_expected_profit_increasing_differences
-- name    : RiskExposure.Complementarity.expected_profit_increasing_differences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:55.063929+00:00
-- url     : https://prove2.me/theorems/d7b498d7-0a4e-41f4-984a-847389b8763e
-- title:
--   Internet Appendix p. 10 — the game is supermodular: E[Π_i] has increasing differences in (Z_i, Z_m)
-- statement:
--   In the setting of the mission, with $P$ satisfying $P(z)\in(0,1)$ and Assumption 1 on $[\underline Z,\overline Z]$, let $i\ne m$ be two banks, $Z\in[\underline Z,\overline Z]^N$, $Z'_m\in[\underline Z,\overline Z]$ with $Z_m\le Z'_m$, and $Z'$ equal to $Z$ with $Z_m$ replaced by $Z'_m$. For all $z\le z'$ in $[\underline Z,\overline Z]$,
--   $$\mathbb E[\Pi_i(\omega;z',Z_{-i})]-\mathbb E[\Pi_i(\omega;z,Z_{-i})]\ \le\ \mathbb E[\Pi_i(\omega;z',Z'_{-i})]-\mathbb E[\Pi_i(\omega;z,Z'_{-i})].$$
--
--   Bank $i$'s expected profit has increasing differences in its own risk exposure and any other bank's: the discrete form of $\partial^2\mathbb E[\Pi_i]/\partial Z_i\partial Z_m\ge0$, so the risk-taking game is supermodular.
--
--   **Formalization Note** The page concludes $d^2\mathbb E[\Pi_i(\omega;Z)]/dZ_i\,dZ_m>0$. No differentiability of $P$ is assumed, so the cross-partial is replaced by increasing differences, and the strict sign by the weak one (it is zero when $i$ and $m$ are not path-connected).
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 10, last paragraph of the proof of Proposition 1

import Mathlib
import Definitions.Def_RiskExposure_Complementarity_Model

namespace RiskExposure.Complementarity

theorem expected_profit_increasing_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (i m : ι) (hmi : m ≠ i) (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi)
    (zm' : ℝ) (hzm' : zm' ∈ Set.Icc Zlo Zhi) (hle : Z m ≤ zm')
    (z z' : ℝ) (hz : z ∈ Set.Icc Zlo Zhi) (hz' : z' ∈ Set.Icc Zlo Zhi) (hzz : z ≤ z') :
    expProfit dbar v P (Function.update Z i z') i - expProfit dbar v P (Function.update Z i z) i ≤
      expProfit dbar v P (Function.update (Function.update Z m zm') i z') i
        - expProfit dbar v P (Function.update (Function.update Z m zm') i z) i := by sorry

end RiskExposure.Complementarity
