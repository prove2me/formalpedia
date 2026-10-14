-- Prove2me | Theorems.Thm_RiskExposure_Complementarity_proposition_1
-- name    : RiskExposure.Complementarity.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:54.382277+00:00
-- url     : https://prove2.me/theorems/31677c53-a40e-4c51-9e35-33f55793a7f4
-- title:
--   Proposition 1, p. 10 — in any financial network, bank i's optimal risk exposure is increasing in every other bank's Z_m
-- statement:
--   Consider $N$ banks with interbank liabilities $\bar d_{ij}\ge0$ (bank $j$ owes bank $i$), all totals $\bar d_j>0$, deposits $v_i>0$, a project set $[\underline Z,\overline Z]$ with $\underline Z\ge v_i+\bar d_i$ for every $i$ (no systemic default), and a success probability $P$ with $P(z)\in(0,1)$, $P$ decreasing and $P(z)\,z$ concave on $[\underline Z,\overline Z]$ (Assumption 1). Payments clear at the greatest payment equilibrium, and $\hat Z_i(Z_{-i})=\operatorname{argmax}_{Z_i\in[\underline Z,\overline Z]}\mathbb E[\Pi_i(\omega;Z)]$ is bank $i$'s best-response set.
--
--   Let $i\ne m$ be banks, $Z\in[\underline Z,\overline Z]^N$, $Z'_m\in[\underline Z,\overline Z]$ with $Z_m\le Z'_m$, and $Z'$ equal to $Z$ with $Z_m$ replaced by $Z'_m$. If $\hat z\in\hat Z_i(Z_{-i})$ and $\hat z'\in\hat Z_i(Z'_{-i})$, then
--   $$\max(\hat z,\hat z')\in\hat Z_i(Z'_{-i})\qquad\text{and}\qquad\min(\hat z,\hat z')\in\hat Z_i(Z_{-i}).$$
--
--   In words: in any financial network, regular or not, risk exposures are strategic complements — bank $i$'s optimal risk exposure is nondecreasing in every other bank's risk exposure.
--
--   **Formalization Note** The paper writes $d\hat Z_i/dZ_m\ge0$, which presupposes a unique, differentiable maximizer; Assumption 1 gives neither. The statement above is the strong-set-order form of "$\hat Z_i$ is nondecreasing in $Z_m$" (Topkis; Milgrom–Shannon). It implies $\hat z\le\hat z'$ whenever both best-response sets are singletons, and $d\hat Z_i/dZ_m\ge0$ for any differentiable selection. It is vacuous when a best-response set is empty, as the paper's $\hat Z_i$ presupposes a maximizer. No regularity or path-connectedness of the network is assumed, and self-loops $\bar d_{ii}>0$ are allowed.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), p. 10, Proposition 1; proof Internet Appendix pp. 7–10

import Mathlib
import Definitions.Def_RiskExposure_Complementarity_Model

namespace RiskExposure.Complementarity

theorem proposition_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (i m : ι) (hmi : m ≠ i) (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi)
    (zm' : ℝ) (hzm' : zm' ∈ Set.Icc Zlo Zhi) (hle : Z m ≤ zm')
    (zh zh' : ℝ) (hzh : zh ∈ bestResponse dbar v P Zlo Zhi Z i)
    (hzh' : zh' ∈ bestResponse dbar v P Zlo Zhi (Function.update Z m zm') i) :
    max zh zh' ∈ bestResponse dbar v P Zlo Zhi (Function.update Z m zm') i ∧
      min zh zh' ∈ bestResponse dbar v P Zlo Zhi Z i := by sorry

end RiskExposure.Complementarity
