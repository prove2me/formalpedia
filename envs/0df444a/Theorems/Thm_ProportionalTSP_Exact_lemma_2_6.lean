-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_lemma_2_6
-- name    : ProportionalTSP.Exact.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:22.533058+00:00
-- url     : https://prove2.me/theorems/51d2c1c1-1509-4f53-ab53-4a8ee5935e88
-- title:
--   Lemma 2.6 — Unique minimum assignment at every feasible load
-- statement:
--   For generic $w$ and every nonnegative integer load $d$ with $\sum_l d_l=k$, the computed canonical assignment is a minimum and is the only minimum:
--   $$d^{A_d}=d,\quad w(A_d)\le w(B)\ (d^B=d),\quad B\text{ minimum at }d\Longrightarrow B=A_d.$$
--   Loads need not be balanced. The result justifies the common canonical-assignment interface.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: the unique minimum-cost assignment for generic costs → a finite argmin with least base-m assignment-rank tie rule, and a default only at infeasible loads; reason: the uniqueness clause is proved in Lemma 2.6; all theorem uses of canonical assignments have feasible loads
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Lemma 2.6, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem lemma_2_6 {m k : ℕ} [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (w : Fin m → Fin k → ℝ) (hw : Generic w) (d : Load m) (hd : feasible k d) :
    MinimumAssignment w d (canonical w d) ∧
      ∀ A : Assignment m k, MinimumAssignment w d A → A = canonical w d := by sorry

end ProportionalTSP.Exact
