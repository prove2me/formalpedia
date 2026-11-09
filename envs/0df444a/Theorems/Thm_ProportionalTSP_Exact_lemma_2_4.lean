-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_lemma_2_4
-- name    : ProportionalTSP.Exact.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:50.142011+00:00
-- url     : https://prove2.me/theorems/33a48094-d6aa-4131-8a7d-611e84e54b82
-- title:
--   Lemma 2.4 — Tight assignments minimize their load cost
-- statement:
--   Let $w$ be any real cross-edge matrix and $a$ any real price vector. If $A$ is tight, then for every assignment $B$ with the same load,
--   $$w(A)\le w(B),\qquad w(B)=w(A)\Longrightarrow B\text{ is tight}.$$
--   This is the fixed-load optimality certificate used by the structural and enumeration results. Genericity is not assumed.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Lemma 2.4, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem lemma_2_4 {m k : ℕ} [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (w : Fin m → Fin k → ℝ) (a : Fin m → ℝ) (A : Assignment m k)
    (hA : TightAssignment w a A) :
    ∀ B : Assignment m k, load B = load A →
      assignmentCost w A ≤ assignmentCost w B ∧
      (assignmentCost w B = assignmentCost w A → TightAssignment w a B) := by sorry

end ProportionalTSP.Exact
