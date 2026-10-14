-- Prove2me | Theorems.Thm_RiskExposure_Complementarity_distortion_star_increasing
-- name    : RiskExposure.Complementarity.distortion_star_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:03.167931+00:00
-- url     : https://prove2.me/theorems/f670ba9f-462b-41a9-a258-8c4db8ae95db
-- title:
--   Internet Appendix p. 10 — D*_i(Z′_{−i}) − D*_i(Z_{−i}) ≥ 0: D*_i is increasing in every other bank's Z_m
-- statement:
--   In the setting of the mission, with $P$ satisfying $P(z)\in(0,1)$ and Assumption 1 on $[\underline Z,\overline Z]$, let $i\ne m$ be two banks, $Z\in[\underline Z,\overline Z]^N$, and $Z'_m\in[\underline Z,\overline Z]$ with $Z_m\le Z'_m$; let $Z'$ be $Z$ with $Z_m$ replaced by $Z'_m$. Then
--   $$\mathcal D^*_i(Z_{-i})\le\mathcal D^*_i(Z'_{-i}),$$
--   where $\mathcal D^*_i(Z_{-i})=\sum_{\omega_{-i}\notin\Omega^{f+}_{-i}}\big[v_i+\big(\bar d_i-\sum_j\theta_{ij}d^*_j(\omega^{i=s})\big)\big]\Pr(\omega_{-i})$.
--
--   In a non-regular network the risk-taking distortion of bank $i$ is carried by the states in which it defaults upon failure; a riskier counterparty both raises the upside cross-subsidy and makes such default more likely, and both effects raise $\mathcal D^*_i$.
--
--   **Formalization Note** The page writes the difference as two sums, each labelled "$>0$". The total is stated with "$\ge$": it is zero when banks $i$ and $m$ are not path-connected. The second sum's factor $v_i+\bar d_i-\sum_j\theta_{ij}d^*_j(\omega^{m=f,i=s})$ is asserted positive on the page without proof.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 10, display D*_i(Z′_{−i}) − D*_i(Z_{−i}); D*_i defined Internet Appendix p. 9

import Mathlib
import Definitions.Def_RiskExposure_Complementarity_Model

namespace RiskExposure.Complementarity

theorem distortion_star_increasing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (i m : ι) (hmi : m ≠ i) (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi)
    (zm' : ℝ) (hzm' : zm' ∈ Set.Icc Zlo Zhi) (hle : Z m ≤ zm') :
    distortionStar dbar v P Z i ≤ distortionStar dbar v P (Function.update Z m zm') i := by sorry

end RiskExposure.Complementarity
