-- Prove2me | Theorems.Thm_RiskExposure_Complementarity_lemma_2
-- name    : RiskExposure.Complementarity.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:51.453223+00:00
-- url     : https://prove2.me/theorems/59104d2b-eca2-40c2-8a1b-927c285c3589
-- title:
--   Lemma 2, p. 8 — the payment equilibrium d*(ω; Z) is constant in the risk exposure vector Z
-- statement:
--   Consider $N$ banks with interbank liabilities $\bar d_{ij}\ge0$, every total liability $\bar d_j=\sum_i\bar d_{ij}$ positive, deposits $v_i>0$, and a project set $[\underline Z,\overline Z]$ satisfying the no-systemic-default assumption $\underline Z\ge v_i+\bar d_i$ for every bank $i$. Let $d^*(\omega;Z)$ be the (greatest) payment equilibrium of state $\omega$ under the risk vector $Z$.
--
--   Then for every state $\omega\in\{s,f\}^N$ and any two risk vectors $Z,Z'$ with all coordinates in $[\underline Z,\overline Z]$,
--   $$d^*(\omega;Z)=d^*(\omega;Z').$$
--
--   Hence one may write $d^*(\omega)$: the payment equilibrium depends on the realized state only, which decouples the clearing problem (2) from the risk-taking game (4).
--
--   **Formalization Note** The profiles are restricted to $[\underline Z,\overline Z]^N$, the paper's project set; outside it a successful bank could default and the claim fails.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), p. 8, Lemma 2; proof Internet Appendix p. 7, (I.2)

import Mathlib
import Definitions.Def_RiskExposure_Complementarity_Model

namespace RiskExposure.Complementarity

theorem lemma_2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo) :
    ∀ (ω : ι → Bool) (Z Z' : ι → ℝ), (∀ j, Z j ∈ Set.Icc Zlo Zhi) →
      (∀ j, Z' j ∈ Set.Icc Zlo Zhi) → paymentEq dbar v ω Z = paymentEq dbar v ω Z' := by sorry

end RiskExposure.Complementarity
