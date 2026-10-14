-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_ring_distortion_le_complete
-- name    : RiskExposure.RingComplete.ring_distortion_le_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:02.314807+00:00
-- url     : https://prove2.me/theorems/8a2a25d4-3664-43f0-8ca3-4b8aa4bc3bae
-- title:
--   Proposition 4 proof, Internet Appendix p. 16 — D^R_i(Z_{−i}) ≤ D^C_i(Z_{−i}) when all other banks choose the same project
-- statement:
--   Let $N\ge2$, $\bar d>0$, $v>0$, let $[\underline Z,\overline Z]$ be the project set with $\underline Z\ge v+\bar d$, and let $P$ satisfy Assumption 1 on $[\underline Z,\overline Z]$. Suppose every bank chooses the same project $z\in[\underline Z,\overline Z]$. Then for every bank $i$, the distortion in the ring network is at most the distortion in the complete network:
--   $$\mathcal D^R_i(Z_{-i})\ \le\ \mathcal D^C_i(Z_{-i}).$$
--
--   A bank in a complete network subsidizes its failed counterparties more, in expectation, than a bank in a ring with the same liabilities and deposits. Through the monotone link between the distortion and the optimal risk exposure, this inequality is what drives Proposition 4.
--
--   **Formalization Note.** The inequality is stated on the model's $\mathcal D_i$ (`distortion`) for the ring and the complete network, at the constant profile $Z_j=z$. The page proves it through the closed forms, which presume one common success probability $P(Z_{-i})$. For heterogeneous profiles it is false: for $N=6$, $\bar d=3.29$, $v=1.22$ and the other banks' failure probabilities $(0.06,0,1,1,1)$, $\mathcal D^C_i-\mathcal D^R_i\approx-1.99$.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 16, proof of Proposition 4, final comparison display ("Now, let's finally compare"); also p. 14, "Because D^C_i(Z_{−i}) is greater than D^R_i(Z_{−i})"

import Mathlib
import Definitions.Def_RiskExposure_RingComplete_Model

namespace RiskExposure.RingComplete

theorem ring_distortion_le_complete (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar)
    (hv : 0 < v) (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (z : ℝ) (hz : z ∈ Set.Icc Zlo Zhi) (i : Fin N) :
    distortion (thetaRing N) dbar v P (fun _ => z) i ≤
      distortion (thetaComplete N) dbar v P (fun _ => z) i := by sorry

end RiskExposure.RingComplete
