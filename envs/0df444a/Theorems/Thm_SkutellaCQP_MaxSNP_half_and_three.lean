-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_half_and_three
-- name    : SkutellaCQP.MaxSNP.half_and_three
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:29.579308+00:00
-- url     : https://prove2.me/theorems/5046d11e-632a-48f4-8fa1-a8e146def811
-- title:
--   §7, proof of Theorem 7.2, p. 33 — OPT_SAT(I) ≥ m/2 and n ≤ 3m
-- statement:
--   Let $I$ be an instance of 3-OCCURRENCE MAX3SAT with $n$ variables and $m$ clauses: every clause has one to three literals, every variable occurs at most three times and at least once. Then an optimal truth assignment satisfies at least half of the clauses, and the number of variables is at most three times the number of clauses:
--   $$
--   \mathrm{OPT}_{\mathrm{SAT}}(I)\ \ge\ \frac m2,\qquad n\ \le\ 3m.
--   $$
--
--   These two counting facts convert the identity of Lemma 7.1 b) into the first condition of an L-reduction.
--
--   **Formalization Note** The first inequality needs every clause to be nonempty, and the second needs every variable to occur; both are part of the validity hypothesis (see the definitions file). The page states the two facts without proof.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 33, §7, proof of Theorem 7.2, second paragraph (first sentence)

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

namespace SkutellaCQP.MaxSNP

/-- Proof of Theorem 7.2 (p. 33): an optimal truth assignment satisfies at least `m/2` clauses,
and `n ≤ 3m`. -/
theorem half_and_three {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid) :
    (m : ℝ) / 2 ≤ optSat I ∧ n ≤ 3 * m := by sorry

end SkutellaCQP.MaxSNP
