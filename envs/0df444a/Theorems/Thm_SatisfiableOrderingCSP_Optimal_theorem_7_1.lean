-- Prove2me | Theorems.Thm_SatisfiableOrderingCSP_Optimal_theorem_7_1
-- name    : SatisfiableOrderingCSP.Optimal.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:50:09.302773+00:00
-- url     : https://prove2.me/theorems/86b06d97-9957-4afd-adcd-9b6babf88004
-- title:
--   Theorem 7.1 — SDP-to-hardness transfer
-- statement:
--   Assume the Rich 2-to-1 Games Conjecture. Fix any finite rationally weighted ordering instance I admitting a basic SDP solution on some positive finite ordered domain, and write s=value(I). For every real epsilon>0 it is NP-hard, by deterministic polynomial-time reductions, to distinguish completely satisfiable instances from instances of value at most s+epsilon. All output predicates occur in I, every output constraint has distinct arguments, and the outputs are unweighted lists with possible repetitions. Sparsity, connectedness, and positive definiteness are not additional hypotheses on I.
--
--   Differences from the source:
--   - encoding: finite indexed sets [n] and positive normalized weighted ordering instances → zero-based Fin indices, indexed repeated constraints, injective scopes, and strictly positive real weights of total one; reason: reindexing changes no instances; isolated variables remain allowed and positive total mass excludes an empty constraint list
--   - encoding: NP-hardness of distinguishing the printed two threshold predicates for every positive error → the published GapNPHard reduction predicate with concrete encodings, also when the Yes and No thresholds overlap; reason: the prescribed reduction convention imposes no disjointness hypothesis and does not exclude large errors or threshold one
--   - encoding: fixed rational base weights and unweighted reduction output in section 7 → a RationalInstance with exact rational witnesses and an explicitly encoded unweighted target; reason: this is the stated computational domain of the hardness reduction; the mathematical LP and SDP models still permit arbitrary real probabilities
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission, sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc, Theorem 7.1, printed p. 39 (PDF p. 42); citation_basis: published.

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Sampling

open scoped BigOperators
open SatisfiableOrderingCSP.Optimal

namespace SatisfiableOrderingCSP.Optimal

theorem theorem_7_1 (hRich : RichGamesConjecture) (I : RationalInstance)
    (q : ℕ) (hsdp : HasBasicSDP I.instanceData q) (ε : ℝ) (hε : 0 < ε) :
    OrderingGapHard (fun φ => ∃ c, (I.instanceData.constraint c).predicate = φ)
      (I.instanceData.value + ε) := by sorry

end SatisfiableOrderingCSP.Optimal
