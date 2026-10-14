-- Prove2me | Theorems.Thm_RiskExposure_Complementarity_eq_I4_distortion_increasing
-- name    : RiskExposure.Complementarity.eq_I4_distortion_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:56.757751+00:00
-- url     : https://prove2.me/theorems/82b8a24e-24e3-4015-a763-be0d4f746a5a
-- title:
--   (I.4), Internet Appendix p. 8 — the cross-subsidy D_i(Z_{−i}) is increasing in every other bank's Z_m
-- statement:
--   In the setting of the mission, with $P$ satisfying $P(z)\in(0,1)$ and Assumption 1 on $[\underline Z,\overline Z]$, let $i\ne m$ be two banks, let $Z\in[\underline Z,\overline Z]^N$, and let $Z'_m\in[\underline Z,\overline Z]$ with $Z_m\le Z'_m$. Write $Z'$ for $Z$ with its $m$-th coordinate replaced by $Z'_m$. Then
--   $$\mathcal D_i(Z_{-i})\le\mathcal D_i(Z'_{-i}).$$
--
--   A riskier counterparty raises the expected net payment bank $i$ makes to the network upon success; this is the regular-network channel of Proposition 1.
--
--   **Formalization Note** The paper considers $Z'_m>Z_m$; the weak inequality $Z_m\le Z'_m$ adds only the trivial equal case.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 8, (I.4)

import Mathlib
import Definitions.Def_RiskExposure_Complementarity_Model

namespace RiskExposure.Complementarity

theorem eq_I4_distortion_increasing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (i m : ι) (hmi : m ≠ i) (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi)
    (zm' : ℝ) (hzm' : zm' ∈ Set.Icc Zlo Zhi) (hle : Z m ≤ zm') :
    distortion dbar v P Z i ≤ distortion dbar v P (Function.update Z m zm') i := by sorry

end RiskExposure.Complementarity
