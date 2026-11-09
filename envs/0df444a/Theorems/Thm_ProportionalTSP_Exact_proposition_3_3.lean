-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_proposition_3_3
-- name    : ProportionalTSP.Exact.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:10.414072+00:00
-- url     : https://prove2.me/theorems/e9579fd0-7f2b-458c-ab4c-22e1546dfe53
-- title:
--   Proposition 3.3 — The prescribed enumeration has no repetitions
-- statement:
--   Under genericity, the output list of the prescribed balanced-load and proper-coloring process has no duplicate subsets and covers precisely $\mathcal C(w)$. In particular,
--   $$|\mathcal C(w)|=N_{m,k}.$$
--   Complementary subsets remain different members. This equality is also required by the full statement of Proposition 3.4.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: the unique minimum-cost assignment for generic costs → a finite argmin with least base-m assignment-rank tie rule, and a default only at infeasible loads; reason: the uniqueness clause is proved in Lemma 2.6; all theorem uses of canonical assignments have feasible loads
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Proposition 3.3, PDF p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem proposition_3_3 {m k : ℕ} [NeZero m] [NeZero k] (hkm : k ≤ m)
    (w : Fin m → Fin k → ℝ) (hw : Generic w) :
    (enumeration w).Nodup ∧ (enumeration w).toFinset = compatibleFamily w ∧
      (compatibleFamily w).card = outputCount m k := by sorry

end ProportionalTSP.Exact
