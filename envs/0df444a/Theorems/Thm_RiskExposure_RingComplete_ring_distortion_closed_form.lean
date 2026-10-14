-- Prove2me | Theorems.Thm_RiskExposure_RingComplete_ring_distortion_closed_form
-- name    : RiskExposure.RingComplete.ring_distortion_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:58.453891+00:00
-- url     : https://prove2.me/theorems/4b6394f1-724a-40ed-b743-35d3b649b818
-- title:
--   D^R closed form, Internet Appendix p. 16 (= p. 14) — D^R_i = Σ_m [d̄ − Σ_{l≤m} (d̄ − lv)⁺ C(N−2−l, N−2−m)/C(N−1, m)] Pr(m banks failed)
-- statement:
--   Let $N\ge2$, $\bar d>0$, $v>0$, let $[\underline Z,\overline Z]$ be the project set with $\underline Z\ge v+\bar d$, and let $P$ satisfy Assumption 1 on $[\underline Z,\overline Z]$. Suppose every bank chooses the same project $z\in[\underline Z,\overline Z]$, and write $q=P(z)$ and $\Pr(m\text{ banks failed})=\binom{N-1}{m}(1-q)^mq^{N-1-m}$. Then bank $i$'s distortion in the ring network $\Theta^R$ is
--   $$\mathcal D^R_i(Z_{-i})=\sum_{m=1}^{N-1}\Big[\bar d-\sum_{l=0}^{m}(\bar d-lv)^+\,w_{m,l}\Big]\Pr(m\text{ banks failed}),$$
--   where $w_{m,l}=\binom{N-2-l}{N-2-m}\big/\binom{N-1}{m}$ for $m\le N-2$, and for $m=N-1$, $w_{m,l}=1$ if $l=N-1$ and $0$ otherwise.
--
--   This is the expectation of the conditional distribution (I.15), and the other side of the comparison behind Proposition 4.
--
--   **Formalization Note.** The statement is made at the constant profile $Z_j=z$ for all $j$, as the page's single $P(Z_{-i})$ presumes. The weight $w_{m,l}$ is `ringWeight N m l`. At $m=N-1$ the printed binomial has lower index $-1$; the convention used, weight one on $l=N-1$, is the value the model gives (every other bank fails, so bank $i$'s upstream chain of failures has length $N-1$). Computing the printed binomial with truncated natural-number subtraction instead would count both $l=N-2$ and $l=N-1$ and give a different, wrong formula.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 16, proof of Proposition 4, display after "Taking the expectation"; also the D^R formula of p. 14

import Mathlib
import Definitions.Def_RiskExposure_RingComplete_Model

namespace RiskExposure.RingComplete

theorem ring_distortion_closed_form (N : ℕ) (hN : 2 ≤ N) (dbar v : ℝ) (hdbar : 0 < dbar)
    (hv : 0 < v) (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : v + dbar ≤ Zlo)
    (P : ℝ → ℝ) (hP01 : ∀ z ∈ Set.Icc Zlo Zhi, 0 < P z ∧ P z < 1)
    (hPanti : AntitoneOn P (Set.Icc Zlo Zhi))
    (hPconc : ConcaveOn ℝ (Set.Icc Zlo Zhi) (fun z => P z * z))
    (z : ℝ) (hz : z ∈ Set.Icc Zlo Zhi) (i : Fin N) :
    distortion (thetaRing N) dbar v P (fun _ => z) i =
      ∑ m ∈ Finset.Icc 1 (N - 1),
        (dbar - ∑ l ∈ Finset.range (m + 1), max (dbar - (l : ℝ) * v) 0 * ringWeight N m l) *
          prFail N m (P z) := by sorry

end RiskExposure.RingComplete
