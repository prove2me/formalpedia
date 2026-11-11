-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_9
-- name    : StochMatchQuery.Union.claim_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:25.437776+00:00
-- url     : https://prove2.me/theorems/11e987f4-7dd5-45d0-abf9-7c28eb032773
-- title:
--   Claim 3.9 — One round
-- statement:
--   Use the round of §§3.1–3.2 with $D\ge1$, $h\in(0,1)$, $L,\ell,d,t$ as in (3.2), a random graph $F$ of maximum degree at most $D$, and matchings $M,B\subseteq F$. Conditional on $F$, the reference $B$ is independent of $M$. Cuts and both sets of proposal uniforms are independent of these inputs. Candidates, signatures, signed increments and tables are those defined in the round bundle.
--
--   For every edge $e$ the actual round has the exact marginal recurrence
--   $$\Pr(e\in M_{\rm new})=(1-t)\Pr(e\in M)+t\Pr(e\in B').$$
--   The cut matching may depend on the current matching; its marginal is not replaced by an independent copy.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
--   - encoding: independent finite random cuts and uniform proposal coins → cuts are computed from independent real uniforms and proposals use exact real thresholds; reason: floor and modulo give the source finite uniform choices; no probabilities are discretized
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.9, PDF/printed p.18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 9; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_9 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : RoundInput G) (D : ℕ) (h : ℝ)
    (hD : 1 ≤ D) (hh : 0 < h ∧ h < 1)
    (hd : ∀ z, 0 < prob q.law (fun a => a = z) → maxDegree G z.1 ≤ D) (e : Edge G) :
    prob (RoundInput.fullLaw G q) (fun z => e ∈ RoundInput.next G q D h z) =
      (1-roundRate D h) * prob q.law (fun z => e ∈ z.2.1) +
      roundRate D h * prob (RoundInput.baseLaw G q) (fun z => e ∈ roundB' G h z) := by sorry

end
end StochMatchQuery.Union
