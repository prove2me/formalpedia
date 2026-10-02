-- Prove2me | Theorems.Thm_ProcessingNetworks_GlobalStability_reentrant_line_globally_stable_iff
-- name    : ProcessingNetworks.GlobalStability.reentrant_line_globally_stable_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:16:21.887235+00:00
-- url     : https://prove2.me/theorems/a10c63dc-23b4-4229-bcf8-3469d243a54b
-- title:
--   Theorem 8.25 — the Rybko-Stolyar-style boundary for a re-entrant line (goal)
-- statement:
--   This is the goal theorem of the mission — the book's version of the field's most cited
--   boundary-of-stability result: subcriticality alone does not suffice for global stability, and
--   a genuinely different "virtual station condition" is both necessary and sufficient alongside
--   it.
--
--   **Theorem 8.25.** The two-station, five-class re-entrant queueing network's fluid model
--   (Figure 8.3) is globally stable if and only if
--   $$
--   \lambda_1(m_1+m_3+m_5) < 1, \qquad \lambda_1(m_2+m_4) < 1, \qquad \lambda_1(m_2+m_5) < 1.
--   $$
--   The first two together are equivalent to the standard load condition $\rho < e$; the third is
--   a separate "virtual station condition" (Dai and Vande Vate's term), the direct analogue of
--   the Rybko–Stolyar network's own extra requirement.
--
--   Sufficiency is proved via the piecewise-linear Lyapunov function $h=\max(G_1,G_2)$ and
--   Lemmas 8.26-8.27; necessity is shown by exhibiting an unstable fluid model solution — one
--   that cycles outward, echoing the Rybko–Stolyar construction of Section 6.2 — under the
--   *extreme* SBP policy giving top priority to class 5 at station 1 and class 2 at station 2,
--   whenever (8.49) fails.
--
--   **Formalization note.** Stated as a single `↔`, with neither direction's proof machinery
--   (the Lyapunov witnesses of Lemma 8.27, or the extreme-SBP instability construction) exposed
--   in the statement — matching the theorem's own "if and only if" exactly. `reentrantLineData`
--   fixes the network's routing and station structure (Figure 8.3, cross-checked against Lemma
--   8.26's own computations — see that network's formalization note); $\lambda_1, m_1,\dots,m_5$
--   remain free parameters, matching the theorem's universal quantification over all positive
--   values of the model data.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 155, Theorem 8.25

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel
import Definitions.Def_ProcessingNetworks_GlobalStability_ReentrantLine

namespace ProcessingNetworks.GlobalStability

/-- Theorem 8.25, Dai & Harrison p. 155 (PDF p. 171) — the goal theorem of this mission: the
two-station, five-class re-entrant queueing network's fluid model is globally stable if and only
if `λ1(m1+m3+m5) < 1` (8.47), `λ1(m2+m4) < 1` (8.48), and `λ1(m2+m5) < 1` (8.49). Conditions
(8.47)-(8.48) together are equivalent to the standard load condition; (8.49) is a separate
"virtual station condition," the analogue of the Rybko-Stolyar network's boundary-of-stability
requirement. -/
theorem reentrant_line_globally_stable_iff
    (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5) :
    FluidModelGloballyStable (reentrantLineData lam1 m1 m2 m3 m4 m5) ↔
      (lam1 * (m1 + m3 + m5) < 1 ∧ lam1 * (m2 + m4) < 1 ∧ lam1 * (m2 + m5) < 1) := by sorry

end ProcessingNetworks.GlobalStability
