-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_complete_payment_equilibrium
-- name    : RiskExposure.RingComplete.complete_payment_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:55.616044+00:00
-- url     : https://prove2.me/theorems/bb65e4c5-ba6f-4f2a-9f38-894f6b5ee117
-- title:
--   Proposition 4 proof, Internet Appendix p. 15 — complete-network clearing: d^C_i = d̄ if i succeeds, (d̄ − (N−1)v/#successes)⁺ if i fails
-- statement:
--   Consider the complete network $\Theta^C=\frac1{N-1}(\mathbb 1_{N,N}-I_N)$ with $N\ge2$ banks, common total interbank liability $\bar d>0$ and common deposit $v>0$. Let the project set be $[\underline Z,\overline Z]$ with $\underline Z\ge v+\bar d$ (no default upon success), let every bank's project $Z_j$ lie in $[\underline Z,\overline Z]$, and let $\omega\in\{s,f\}^N$ be a state in which at least one bank succeeds. Write $S(\omega)$ for the number of successful banks. Then the greatest payment equilibrium is
--   $$d^C_i(\omega)=\begin{cases}\bar d & \omega_i=s,\\[2pt] \Big(\bar d-\dfrac{N-1}{S(\omega)}\,v\Big)^+ & \omega_i=f.\end{cases}$$
--
--   The factor $(N-1)/S(\omega)$ is $1/\sum_{\omega_j=s}\theta_{ij}$ for a failed bank $i$. Every failed bank pays the same amount, and that amount falls to zero once the failed banks' shortfall exceeds what the successful banks' payments cover. This closed form is the input for the distortion of the complete network, (I.13).
--
--   **Formalization Note.** The hypothesis "at least one bank succeeds" excludes the state in which all banks fail; there every bank pays $0$, and the printed formula would divide by zero. That state never enters $\mathcal D_i$, which conditions on bank $i$'s success. $d^*$ is the greatest solution of (2), as in the model file.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 15, proof of Proposition 4, part (a), display after "So, we can collapse the second and the third lines"

import Mathlib
import Definitions.Def_RiskExposure_RingComplete_Model

namespace RiskExposure.RingComplete

theorem complete_payment_equilibrium (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar)
    (hv : 0 < v) (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (Z : Fin N → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi)
    (ω : Fin N → Bool) (hsucc : ∃ k, ω k = true) :
    ∀ i, paymentEq (thetaComplete N) dbar v ω Z i =
      if ω i then dbar
      else max (dbar - ((N : ℝ) - 1) /
        ((Finset.univ.filter (fun k => ω k = true)).card : ℝ) * v) 0 := by sorry

end RiskExposure.RingComplete
