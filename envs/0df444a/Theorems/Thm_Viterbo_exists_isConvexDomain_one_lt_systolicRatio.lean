-- Prove2me | Theorems.Thm_Viterbo_exists_isConvexDomain_one_lt_systolicRatio
-- name    : Viterbo.exists_isConvexDomain_one_lt_systolicRatio
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:15:55.289925+00:00
-- url     : https://prove2.me/theorems/cdeeee93-5416-47de-9a16-b468ba3eba49
-- title:
--   Theorem 1.3 for c_EHZ — for every n ≥ 2 some convex domain in ℝ²ⁿ has systolic ratio greater than 1
-- statement:
--   For every $n \ge 2$ there is a convex domain $A \subset \mathbb R^{2n}$ with $c_{\rm EHZ}(A)$ finite and $\mathrm{Sys}(A) = c_{\rm EHZ}(A)^n/(n!\,\mathrm{Vol}(A)) > 1$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 5, Theorem 1.3 for the EHZ capacity

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem exists_isConvexDomain_one_lt_systolicRatio (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain A ∧ cEHZ A < ⊤ ∧ 1 < systolicRatio A := by
  sorry

end Viterbo
