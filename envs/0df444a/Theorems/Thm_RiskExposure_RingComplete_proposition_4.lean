-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_proposition_4
-- name    : RiskExposure.RingComplete.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:00.590796+00:00
-- url     : https://prove2.me/theorems/09f8b5a6-954a-4edd-a09e-2d008c20cfee
-- title:
--   Proposition 4, p. 13 — in the least equilibrium, every bank's risk exposure is at least as large in a complete network as in a ring
-- statement:
--   Let $N\ge2$ banks have common total interbank liability $\bar d>0$ and common deposit $v>0$, and let the project set be $[\underline Z,\overline Z]$ with $\underline Z\ge v+\bar d$. Let $P$ be the success-probability function, with $P(z)\in(0,1)$, $P$ decreasing and $P(z)\,z$ concave on $[\underline Z,\overline Z]$ (Assumption 1), and $P$ continuous on $[\underline Z,\overline Z]$. Consider the risk-taking game in the complete network $\Theta^C$ and in the ring network $\Theta^R$, each with the greatest payment equilibrium as $d^*$. Let $Z^C$ be the least risk-taking equilibrium of the complete network and $Z^R$ the least risk-taking equilibrium of the ring. Then
--   $$Z^R_i\ \le\ Z^C_i\qquad\text{for every bank } i .$$
--
--   "The equilibrium" in the paper is its selection of the smallest equilibrium (p. 11). The proposition says that the co-insurance of a complete network raises every bank's equilibrium risk exposure relative to a ring with the same liabilities and deposits, even though each bank's total face-value liability $\bar d+v$ is the same in both.
--
--   **Formalization Note.** The least equilibria are given as hypotheses (`IsLeast` over each network's equilibrium set). Continuity of $P$ on $[\underline Z,\overline Z]$ is not on the page; it is added so that best responses exist and the least equilibria the statement compares exist (Topkis's theorem on supermodular games). "Greater" is read weakly: a strict inequality fails, for instance, for $N=2$, where the two networks coincide, or when both least equilibria sit at $\overline Z$. $d^*$ is the greatest solution of the clearing system.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), p. 13, Proposition 4; equilibrium selection p. 11; proof Internet Appendix pp. 15–16

import Mathlib
import Definitions.Def_RiskExposure_RingComplete_Model

namespace RiskExposure.RingComplete

theorem proposition_4 (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar) (hv : 0 < v)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (hPcont : ContinuousOn P (Set.Icc Zlo Zhi))
    (ZC ZR : Fin N → ℝ)
    (hC : IsLeast {Z | IsEquilibrium (thetaComplete N) dbar v P Zlo Zhi Z} ZC)
    (hR : IsLeast {Z | IsEquilibrium (thetaRing N) dbar v P Zlo Zhi Z} ZR) :
    ∀ i, ZR i ≤ ZC i := by sorry

end RiskExposure.RingComplete
