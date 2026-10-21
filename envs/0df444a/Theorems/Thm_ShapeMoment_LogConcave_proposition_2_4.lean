-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_proposition_2_4
-- name    : ShapeMoment.LogConcave.proposition_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:43.86637+00:00
-- url     : https://prove2.me/theorems/ba80041e-dda2-4a87-bd95-19f0a4eaa702
-- title:
--   Proposition 2.4 — equivalent LC formulations
-- statement:
--   Assume $q_0=1$. The two formulations (DMP-LC) and (DMP-LC′) have the same feasible region:
--
--   $$\mathcal F_{\mathrm{LC}}=\mathcal F_{\mathrm{LC'}}.$$
--
--   Their linear objectives are the same, so equality of feasible sets gives the asserted equivalence. The normalization is the standing convention on page 5.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 6, Proposition 2.4; proof pp. 23–24

import Definitions.Def_ShapeMoment_LogConcave_Model

namespace ShapeMoment.LogConcave

theorem proposition_2_4 (n m : ℕ) (q : ℕ → ℝ) (hq0 : q 0 = 1) :
    feasLC n m q = feasLCPrime n m q := by sorry

end ShapeMoment.LogConcave
