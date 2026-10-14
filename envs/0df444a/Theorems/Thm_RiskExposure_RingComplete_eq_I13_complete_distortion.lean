-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_eq_I13_complete_distortion
-- name    : RiskExposure.RingComplete.eq_I13_complete_distortion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:57.026452+00:00
-- url     : https://prove2.me/theorems/0e7f7b1d-0bcc-42fa-9b64-71f603967d6e
-- title:
--   (I.13), Internet Appendix p. 15 — D^C_i = Σ_m [d̄ − (d̄ − (N−1)v/(N−m))⁺ m/(N−1) − d̄(N−1−m)/(N−1)] Pr(m) = Σ_m min(mv/(N−m), md̄/(N−1)) Pr(m)
-- statement:
--   Let $N\ge2$, $\bar d>0$, $v>0$, and let $[\underline Z,\overline Z]$ be the project set with $\underline Z\ge v+\bar d$. Let $P$ be a success-probability function satisfying Assumption 1 on $[\underline Z,\overline Z]$: $P(z)\in(0,1)$, $P$ is decreasing and $P(z)\,z$ is concave. Suppose every bank chooses the same project $z\in[\underline Z,\overline Z]$, and write $q=P(z)$ and
--   $$\Pr(m\text{ banks failed})=\binom{N-1}{m}(1-q)^m q^{N-1-m}.$$
--   Then bank $i$'s distortion in the complete network $\Theta^C$ is
--   $$\mathcal D^C_i(Z_{-i})=\sum_{m=1}^{N-1}\Big[\bar d-\Big(\bar d-\frac{N-1}{N-m}v\Big)^+\frac{m}{N-1}-\bar d\,\frac{N-1-m}{N-1}\Big]\Pr(m\text{ banks failed})=\sum_{m=1}^{N-1}\min\Big(\frac{m\,v}{N-m},\frac{m\,\bar d}{N-1}\Big)\Pr(m\text{ banks failed}).$$
--
--   In the first form, the middle term is the payment bank $i$ receives from the $m$ failed banks and the last is the payment from the $N-1-m$ successful ones. The second form, (I.13), shows that $\mathcal D^C_i$ is an expectation of $\min(mv/(N-m),\,m\bar d/(N-1))$ over the binomial number of failed counterparties. It is one side of the comparison behind Proposition 4.
--
--   **Formalization Note.** The statement is made at the constant profile $Z_j=z$ for all $j$, because the page's single $P(Z_{-i})$ presumes the other banks choose the same project; $\mathcal D_i$ does not depend on $Z_i$. All differences $N-1$, $N-m$, $N-1-m$ are taken in $\mathbb R$; for $1\le m\le N-1$ they are nonnegative, and $N-m\ge1$.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 15, proof of Proposition 4, (I.13); the first line is also the D^C formula of p. 14

import Mathlib
import Definitions.Def_RiskExposure_RingComplete_Model

namespace RiskExposure.RingComplete

theorem eq_I13_complete_distortion (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar)
    (hv : 0 < v) (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (z : ℝ) (hz : z ∈ Set.Icc Zlo Zhi) (i : Fin N) :
    distortion (thetaComplete N) dbar v P (fun _ => z) i =
        ∑ m ∈ Finset.Icc 1 (N - 1),
          (dbar - max (dbar - ((N : ℝ) - 1) / ((N : ℝ) - m) * v) 0 * ((m : ℝ) / ((N : ℝ) - 1))
            - dbar * (((N : ℝ) - 1 - m) / ((N : ℝ) - 1))) * prFail N m (P z) ∧
      distortion (thetaComplete N) dbar v P (fun _ => z) i =
        ∑ m ∈ Finset.Icc 1 (N - 1),
          min ((m : ℝ) * v / ((N : ℝ) - m)) ((m : ℝ) * dbar / ((N : ℝ) - 1)) *
            prFail N m (P z) := by sorry

end RiskExposure.RingComplete
