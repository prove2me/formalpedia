-- Prove2me | Theorems.Thm_ProcessingNetworks_GlobalStability_assembly_side_business_stable
-- name    : ProcessingNetworks.GlobalStability.assembly_side_business_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:13:18.886761+00:00
-- url     : https://prove2.me/theorems/dcbc4688-8670-438b-9cbc-98dfd4af6b51
-- title:
--   Theorem 8.21 — assembly-with-side-business fluid model is stable (milestone)
-- statement:
--   **Theorem 8.21.** Assume the three inequalities of (5.33) — $\lambda_2 > \lambda_1$,
--   $\lambda_1 m_1 < 1$, $(\lambda_2-\lambda_1)m_2 < 1$ — all hold. Then the assembly-with-
--   side-business fluid model is stable.
--
--   The proof uses the piecewise-linear Lyapunov function $f(t) = |Z_1(t)-Z_2(t)| + \alpha Z_1(t)$
--   for a suitably small $\alpha > 0$, case-splitting on the sign of $Z_1(t)-Z_2(t)$ and applying
--   Lemma 8.9 (mission V) when $Z_2(t)=0$; it is the chapter's first genuinely two-dimensional
--   piecewise-linear Lyapunov argument, foreshadowing the ring and re-entrant-line constructions
--   later in the chapter.
--
--   **Formalization note.** The three inequalities are stated exactly as (5.33), with $m_1, m_2$
--   as mean service times (matching the book's own use of "$m$" for times and "$\mu = 1/m$" for
--   rates within the fluid model's own equations, `AssemblySideBusinessFluidModel`).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 150, Theorem 8.21

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_AssemblySideBusiness

namespace ProcessingNetworks.GlobalStability

/-- Theorem 8.21, Dai & Harrison p. 150 (PDF p. 166): for the assembly-with-side-business SPN
(Figure 5.5) under the policy "server 1 assembles whenever both buffers are non-empty; server 2
serves buffer 2 alone whenever `Z1 < Z2`," if `lam2 > lam1`, `lam1 * m1 < 1` and
`(lam2 - lam1) * m2 < 1` (Eq. 5.33), then the fluid model is stable. -/
theorem assembly_side_business_stable
    (lam1 lam2 m1 m2 : ℝ) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (h1 : lam2 > lam1) (h2 : lam1 * m1 < 1) (h3 : (lam2 - lam1) * m2 < 1) :
    AssemblySideBusinessFluidStable lam1 lam2 m1 m2 := by sorry

end ProcessingNetworks.GlobalStability
