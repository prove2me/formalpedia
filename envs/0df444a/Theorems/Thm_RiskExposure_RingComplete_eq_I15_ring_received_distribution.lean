-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_eq_I15_ring_received_distribution
-- name    : RiskExposure.RingComplete.eq_I15_ring_received_distribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:57.791534+00:00
-- url     : https://prove2.me/theorems/35427b0d-e449-4f2e-854e-1eb736654371
-- title:
--   (I.15), Internet Appendix p. 16 — in the ring, given m failures, bank i receives (d̄ − lv)⁺ with probability C(N−2−l, N−2−m)/C(N−1, m)
-- statement:
--   Consider the ring network $\Theta^R$ with $N\ge2$ banks, $\bar d>0$, $v>0$, project set $[\underline Z,\overline Z]$ with $\underline Z\ge v+\bar d$, and every $Z_j\in[\underline Z,\overline Z]$. Fix a bank $i$. For a state $\omega$ in which bank $i$ succeeds, let $l(\omega)$ be the number of consecutive failed upstream neighbours $i-1,i-2,\dots$ of $i$ before the first successful bank. Then:
--
--   1. For $0\le l\le m\le N-2$, the number of states in which bank $i$ succeeds, exactly $m$ banks fail and $l(\omega)=l$ is $\binom{N-2-l}{N-2-m}$.
--   2. In every state in which bank $i$ succeeds, the total interbank payment it receives is
--   $$\sum_j\theta_{ij}d^R_j(\omega)=\big(\bar d-l(\omega)\,v\big)^+ .$$
--   3. In every state in which bank $i$ succeeds and all $N-1$ other banks fail, $l(\omega)=N-1$.
--
--   Since all $\binom{N-1}{m}$ placements of the $m$ failures among the other banks are equally likely when the other banks choose the same project, parts 1–3 are the conditional distribution (I.15): given $m$ failures, bank $i$ receives $(\bar d-lv)^+$ with probability $\binom{N-2-l}{N-2-m}\big/\binom{N-1}{m}$ for $m\le N-2$, and $(\bar d-(N-1)v)^+$ with probability one for $m=N-1$. Taking expectations gives the closed form of the ring distortion.
--
--   **Formalization Note.** $l(\omega)$ is `upRun ω i`, the run length $K_{i-1}(\omega)$ of the upstream neighbour. The page states (I.15) as a conditional distribution; here it is split into its counting content (part 1), the value received (part 2), and the row $m=N-1$ (part 3), where the printed binomial $\binom{N-2-l}{N-2-m}$ has lower index $-1$ and the model's answer is weight one at $l=N-1$.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 16, proof of Proposition 4, part (b), (I.15) and the paragraph after it

import Mathlib
import Definitions.Def_RiskExposure_RingComplete_Model

namespace RiskExposure.RingComplete

theorem eq_I15_ring_received_distribution (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar)
    (hv : 0 < v) (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (Z : Fin N → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi) (i : Fin N) :
    (∀ l m : ℕ, l ≤ m → m + 2 ≤ N →
      (Finset.univ.filter (fun ω : Fin N → Bool =>
          ω i = true ∧ (Finset.univ.filter (fun k => ω k = false)).card = m ∧
            upRun ω i = l)).card = (N - 2 - l).choose (N - 2 - m)) ∧
    (∀ ω : Fin N → Bool, ω i = true →
      ∑ j, thetaRing N i j * paymentEq (thetaRing N) dbar v ω Z j =
        max (dbar - (upRun ω i : ℝ) * v) 0) ∧
    (∀ ω : Fin N → Bool, ω i = true →
      (Finset.univ.filter (fun k => ω k = false)).card = N - 1 → upRun ω i = N - 1) := by sorry

end RiskExposure.RingComplete
