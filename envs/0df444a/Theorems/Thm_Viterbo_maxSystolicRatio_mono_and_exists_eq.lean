-- Prove2me | Theorems.Thm_Viterbo_maxSystolicRatio_mono_and_exists_eq
-- name    : Viterbo.maxSystolicRatio_mono_and_exists_eq
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:18:12.40873+00:00
-- url     : https://prove2.me/theorems/4f24676c-4a77-49fe-aaa0-34af2b2371d4
-- title:
--   §1.1(ii) — Sys(K²ⁿ) ≤ Sys(K²ᵐ) for n ≤ m, and the supremum Sys(K²ⁿ) is finite and attained
-- statement:
--   Let $n \ge 1$ and let $\mathrm{Sys}(\mathcal K^{2n})$ be the supremum of $\mathrm{Sys}(A)$ over the convex domains $A \subset \mathbb R^{2n}$. Then $\mathrm{Sys}(\mathcal K^{2n}) \le \mathrm{Sys}(\mathcal K^{2m})$ for every $m \ge n$, $\mathrm{Sys}(\mathcal K^{2n})$ is finite, and some convex domain $A \subset \mathbb R^{2n}$ has $\mathrm{Sys}(A) = \mathrm{Sys}(\mathcal K^{2n})$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 6, the monotonicity and attainment of the maximal systolic ratio

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem maxSystolicRatio_mono_and_exists_eq (n : ℕ) (hn : 1 ≤ n) :
    (∀ m, n ≤ m → maxSystolicRatio n ≤ maxSystolicRatio m) ∧ maxSystolicRatio n < ⊤ ∧
      ∃ A : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain A ∧ systolicRatio A = maxSystolicRatio n := by
  sorry

end Viterbo
