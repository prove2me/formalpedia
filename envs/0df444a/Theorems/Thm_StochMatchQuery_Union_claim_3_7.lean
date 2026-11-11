-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_7
-- name    : StochMatchQuery.Union.claim_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:34.428079+00:00
-- url     : https://prove2.me/theorems/8f4f63e7-18cf-474c-8613-d49363236408
-- title:
--   Claim 3.7 — Simultaneous toggles
-- statement:
--   Use the round of §§3.1–3.2 with $D\ge1$, $h\in(0,1)$, $L,\ell,d,t$ as in (3.2), a random graph $F$ of maximum degree at most $D$, and matchings $M,B\subseteq F$. Conditional on $F$, the reference $B$ is independent of $M$. Cuts and both sets of proposal uniforms are independent of these inputs. Candidates, signatures, signed increments and tables are those defined in the round bundle.
--
--   For every legal outcome the simultaneous update is a matching and, for every edge $e$,
--   $$1_{\{e\in M_{\rm new}\}}=1_{\{e\in M\}}+\sum_{c\in\mathcal C}1_{\{c\in S\}}\Delta_e(c).$$
--   This is a pointwise identity, including negative exchanges, rather than an expected-weight inequality.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
--   - encoding: independent finite random cuts and uniform proposal coins → cuts are computed from independent real uniforms and proposals use exact real thresholds; reason: floor and modulo give the source finite uniform choices; no probabilities are discretized
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.7, PDF/printed p.18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 7; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_7 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : RoundInput G) (D : ℕ) (h : ℝ)
    (hD : 1 ≤ D) (hh : 0 < h ∧ h < 1)
    (hd : ∀ z, 0 < prob q.law (fun a => a = z) → maxDegree G z.1 ≤ D) :
    ∀ z : RoundOutcome G, 0 < prob q.law (fun a => a = z.1.1) →
      (∀ c, 0 ≤ z.1.2 c ∧ z.1.2 c ≤ 1) →
      (∀ c, 0 ≤ z.2.1 c ∧ z.2.1 c ≤ 1) →
      IsMatching G (RoundInput.next G q D h z) ∧ ∀ e,
      ind (e ∈ RoundInput.next G q D h z) = ind (e ∈ roundM G z.1) +
        ∑ c ∈ candidates G (pieceLength h), ind (c ∈ RoundInput.kept G q D h z) *
          delta G (roundF G z.1) (roundM G z.1) c e := by sorry

end
end StochMatchQuery.Union
