-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_2
-- name    : StochMatchQuery.Union.claim_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:06.478268+00:00
-- url     : https://prove2.me/theorems/e219ea7a-f16f-483e-9725-f9ed0368f596
-- title:
--   Claim 3.2 — Cutting
-- statement:
--   Use the round of §§3.1–3.2 with $D\ge1$, $h\in(0,1)$, $L,\ell,d,t$ as in (3.2), a random graph $F$ of maximum degree at most $D$, and matchings $M,B\subseteq F$. Conditional on $F$, the reference $B$ is independent of $M$. Cuts and both sets of proposal uniforms are independent of these inputs. Candidates, signatures, signed increments and tables are those defined in the round bundle.
--
--   The cut matching is a matching; every component of $M\triangle B'$ is an alternating simple path or cycle of length at most $\ell$. For every input outcome and $e\in B$,
--   $$\Pr(e\in B'\mid F,M,B)\ge1-2/L,\qquad (1-2/L)\mu_e\le\Pr(e\in B')\le\mu_e,$$
--   where $\mu_e=\Pr(e\in B)$. The conditional assertion is represented by integrating only the cut coordinates. Both the geometric and marginal conclusions are retained.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
--   - encoding: independent finite random cuts and uniform proposal coins → cuts are computed from independent real uniforms and proposals use exact real thresholds; reason: floor and modulo give the source finite uniform choices; no probabilities are discretized
--   - encoding: every component of M△B′ is an alternating path or cycle with at most ℓ edges → every component of M△B′ is a candidate (simple path or cycle with 1 to ℓ edges); alternation is not restated; reason: M is a matching on the support and B′ is a matching by the first clause, so every component of M△B′ alternates; no instance changes
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.2, PDF/printed p.13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 2; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : RoundInput G) (D : ℕ) (h : ℝ)
    (hD : 1 ≤ D) (hh : 0 < h ∧ h < 1)
    (hd : ∀ z, 0 < prob q.law (fun a => a = z) → maxDegree G z.1 ≤ D) :
    (∀ z : RoundBase G, 0 < prob q.law (fun a => a = z.1) →
      (∀ c, 0 ≤ z.2 c ∧ z.2 c ≤ 1) →
      IsMatching G (roundB' G h z) ∧
      ∀ c, component G (toggle G (roundM G z) (roundB' G h z)) c →
        c ∈ candidates G (pieceLength h)) ∧
    (∀ z, 0 < prob q.law (fun a => a = z) → ∀ e ∈ z.2.2,
      prob (cutLaw G) (fun u => e ∈ cutMatching G (cutPeriod h) z.2.1 z.2.2 u) ≥
        1 - 2/(cutPeriod h : ℝ)) ∧
    (∀ e, (1-2/(cutPeriod h : ℝ)) * prob q.law (fun z => e ∈ z.2.2) ≤
      prob (RoundInput.baseLaw G q) (fun z => e ∈ roundB' G h z) ∧
      prob (RoundInput.baseLaw G q) (fun z => e ∈ roundB' G h z) ≤
        prob q.law (fun z => e ∈ z.2.2)) := by sorry

end
end StochMatchQuery.Union
