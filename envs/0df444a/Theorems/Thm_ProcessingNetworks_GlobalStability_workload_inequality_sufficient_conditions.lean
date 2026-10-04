-- Prove2me | Theorems.Thm_ProcessingNetworks_GlobalStability_workload_inequality_sufficient_conditions
-- name    : ProcessingNetworks.GlobalStability.workload_inequality_sufficient_conditions
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:14:51.910873+00:00
-- url     : https://prove2.me/theorems/f1c0cabf-be0b-49bb-bf8c-747685fd263c
-- title:
--   Lemma 8.26 — sufficient conditions for the four workload inequalities (milestone)
-- statement:
--   **Lemma 8.26.** (a) If $x_2,x_4,\varepsilon > 0$ satisfy $\lambda_1(x_2{+}x_4)+\varepsilon \le
--   \mu_2 x_2$ and $\le \mu_4 x_4$ (8.59)-(8.60), then $H_2(t)>0 \Rightarrow \dot G_2(t)\le
--   -\varepsilon$ (8.58). (b) The analogous statement for $x_1,x_3,x_5$ and $H_1, G_1$
--   (8.61)-(8.63) $\Rightarrow$ (8.57). (c) If $x>0$ satisfies $x_2{+}x_4\le x_1{+}x_3{+}x_5$ and
--   $x_4\le x_3{+}x_5$ (8.64)-(8.65), then $H_2(t)=0 \Rightarrow G_1(t)\le G_2(t)$ (8.56). (d) The
--   symmetric statement (8.66)-(8.67) $\Rightarrow$ (8.55).
--
--   These four implications are exactly what Theorem 8.25's Lyapunov argument (via Lemma 8.5)
--   needs to conclude $\dot h(t) \le -\varepsilon$ for the piecewise-linear function
--   $h = \max(G_1,G_2)$, regardless of which of $G_1, G_2$ attains the maximum.
--
--   **Formalization note.** All four parts are bundled as one conjunction, matching the book's
--   single numbered Lemma 8.26 with parts (a)-(d); $\mu_i := 1/m_i$ is written inline as `x_i/m_i`
--   rather than introducing a separate rate vector, and $G_1, G_2, H_1, H_2$ are the concrete
--   functions of `reentrantLineData`'s fluid solution defined alongside that network. The network
--   data are positive ($\lambda_1 > 0$, $m_i > 0$), as throughout Section 8.7; with $m_i \le 0$ the
--   "rates" $x_i/m_i$ would be junk or negative and parts (a)–(b) would be false.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 157, Lemma 8.26

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel
import Definitions.Def_ProcessingNetworks_GlobalStability_ReentrantLine

namespace ProcessingNetworks.GlobalStability

/-- Lemma 8.26, Dai & Harrison p. 157 (PDF p. 173), parts (a)-(d): sufficient algebraic
conditions on a positive weight vector `(x1,…,x5)` and `ε > 0` for the four workload derivative
inequalities (8.55)-(8.58) that Theorem 8.25's Lyapunov argument needs. -/
theorem workload_inequality_sufficient_conditions
    (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (Dh Fh Th Zh : ℝ → Fin 5 → ℝ)
    (hni : IsNonIdlingSolution (reentrantLineData lam1 m1 m2 m3 m4 m5) Dh Fh Th Zh) :
    (∀ x2 x4 ε : ℝ, 0 < x2 → 0 < x4 → 0 < ε →
      lam1 * (x2 + x4) + ε ≤ x2 / m2 → lam1 * (x2 + x4) + ε ≤ x4 / m4 →
      ∀ t : ℝ, 0 < t → 0 < reentrantH2 Zh t →
        ∀ d : ℝ, HasDerivAt (reentrantG2 x2 x4 Zh) d t → d ≤ -ε) ∧
    (∀ x1 x3 x5 ε : ℝ, 0 < x1 → 0 < x3 → 0 < x5 → 0 < ε →
      lam1 * (x1 + x3 + x5) + ε ≤ x1 / m1 → lam1 * (x1 + x3 + x5) + ε ≤ x3 / m3 →
      lam1 * (x1 + x3 + x5) + ε ≤ x5 / m5 →
      ∀ t : ℝ, 0 < t → 0 < reentrantH1 Zh t →
        ∀ d : ℝ, HasDerivAt (reentrantG1 x1 x3 x5 Zh) d t → d ≤ -ε) ∧
    (∀ x1 x2 x3 x4 x5 : ℝ, 0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 →
      x2 + x4 ≤ x1 + x3 + x5 → x4 ≤ x3 + x5 →
      ∀ t : ℝ, 0 < t → reentrantH2 Zh t = 0 →
        reentrantG1 x1 x3 x5 Zh t ≤ reentrantG2 x2 x4 Zh t) ∧
    (∀ x1 x2 x3 x4 x5 : ℝ, 0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 →
      x3 + x5 ≤ x2 + x4 → x5 ≤ x4 →
      ∀ t : ℝ, 0 < t → reentrantH1 Zh t = 0 →
        reentrantG2 x2 x4 Zh t ≤ reentrantG1 x1 x3 x5 Zh t) := by sorry

end ProcessingNetworks.GlobalStability
