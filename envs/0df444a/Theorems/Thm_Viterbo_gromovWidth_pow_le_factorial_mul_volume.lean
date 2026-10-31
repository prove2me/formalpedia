-- Prove2me | Theorems.Thm_Viterbo_gromovWidth_pow_le_factorial_mul_volume
-- name    : Viterbo.gromovWidth_pow_le_factorial_mul_volume
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:21:26.51911+00:00
-- url     : https://prove2.me/theorems/4c8a565c-a314-42c8-bd43-bf9bc94c6eb4
-- title:
--   p. 3 — Viterbo's conjecture holds for the Gromov width
-- statement:
--   For every convex domain $K \subset \mathbb R^{2n}$, $c_G(K)^n \le n!\,\mathrm{Vol}(K)$, where $c_G$ is the Gromov width.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 3, Viterbo's conjecture for the Gromov width

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

open MeasureTheory
open scoped ENNReal

namespace Viterbo

theorem gromovWidth_pow_le_factorial_mul_volume (n : ℕ) (K : Set (OAI.SymmetricPolar.Phase n))
    (hK : IsConvexDomain K) :
    OAI.SymmetricPolar.gromovWidth K ^ n ≤ (n.factorial : ℝ≥0∞) * volume K := by
  sorry

end Viterbo
