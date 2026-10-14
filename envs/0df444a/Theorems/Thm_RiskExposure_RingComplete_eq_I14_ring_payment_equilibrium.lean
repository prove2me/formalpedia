-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_eq_I14_ring_payment_equilibrium
-- name    : RiskExposure.RingComplete.eq_I14_ring_payment_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:00.615604+00:00
-- url     : https://prove2.me/theorems/b0817a60-cf1a-4dcd-a218-9ad714621852
-- title:
--   (I.14), Internet Appendix p. 16 — ring clearing: d^R_i = d̄ if i succeeds, (d̄ − K_i(ω)v)⁺ if i fails
-- statement:
--   Consider the ring network $\Theta^R$ with $N\ge2$ banks, in which bank $i$ is owed $\bar d$ by its upstream neighbour $i-1$ (indices mod $N$), with $\bar d>0$, $v>0$, project set $[\underline Z,\overline Z]$ with $\underline Z\ge v+\bar d$, and every $Z_j\in[\underline Z,\overline Z]$. Let $\omega$ be a state in which at least one bank succeeds, and let
--   $$K_i(\omega)=\min\{o\ge0:\ \omega_{i-o}=s\}$$
--   be the number of consecutive failed banks met going upstream from $i$, starting with $i$ itself, before the first successful bank. Then the greatest payment equilibrium is
--   $$d^R_i(\omega)=\begin{cases}\bar d & \omega_i=s,\\ \big(\bar d-K_i(\omega)\,v\big)^+ & \omega_i=f.\end{cases}$$
--
--   Along a chain of failed banks each one passes on what it receives less its deposit $v$, so the payment shrinks by $v$ per failed bank. This is the ring counterpart of the complete-network clearing formula.
--
--   **Formalization Note.** $K_i$ is `runLength ω i`. When no bank succeeds the minimum does not exist, so the statement assumes some bank succeeds. For a failed bank $K_i\ge1$, so the page's description "the number of failed debtors in the chain before reaching the first successful bank" agrees with $\min\{o:\omega_{i-o}=s\}$ when bank $i$ itself is counted as the first failed debtor of the chain.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 16, proof of Proposition 4, part (b), (I.14)

import Mathlib
import Definitions.Def_RiskExposure_RingComplete_Model

namespace RiskExposure.RingComplete

theorem eq_I14_ring_payment_equilibrium (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar)
    (hv : 0 < v) (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (Z : Fin N → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi)
    (ω : Fin N → Bool) (hsucc : ∃ k, ω k = true) :
    ∀ i, paymentEq (thetaRing N) dbar v ω Z i =
      if ω i then dbar else max (dbar - (runLength ω i : ℝ) * v) 0 := by sorry

end RiskExposure.RingComplete
