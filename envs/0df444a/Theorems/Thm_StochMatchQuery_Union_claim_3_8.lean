-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_8
-- name    : StochMatchQuery.Union.claim_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:55.991685+00:00
-- url     : https://prove2.me/theorems/f7e4a109-839d-4be6-a281-47f41bb7f817
-- title:
--   Claim 3.8 — Pieces transform M into B′
-- statement:
--   Use the round of §§3.1–3.2 with $D\ge1$, $h\in(0,1)$, $L,\ell,d,t$ as in (3.2), a random graph $F$ of maximum degree at most $D$, and matchings $M,B\subseteq F$. Conditional on $F$, the reference $B$ is independent of $M$. Cuts and both sets of proposal uniforms are independent of these inputs. Candidates, signatures, signed increments and tables are those defined in the round bundle.
--
--   In every legal outcome and for every edge $e$,
--   $$\sum_{c\in\mathcal C}1_{\mathcal E_c}\Delta_e(c)=1_{\{e\in B'\}}-1_{\{e\in M\}}.$$
--   The true pieces exactly transform the current matching into the cut reference matching.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
--   - encoding: independent finite random cuts and uniform proposal coins → cuts are computed from independent real uniforms and proposals use exact real thresholds; reason: floor and modulo give the source finite uniform choices; no probabilities are discretized
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.8, PDF/printed p.18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 8; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_8 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : RoundInput G) (D : ℕ) (h : ℝ)
    (hD : 1 ≤ D) (hh : 0 < h ∧ h < 1)
    (hd : ∀ z, 0 < prob q.law (fun a => a = z) → maxDegree G z.1 ≤ D) :
    ∀ z : RoundBase G, 0 < prob q.law (fun a => a = z.1) →
      (∀ c, 0 ≤ z.2 c ∧ z.2 c ≤ 1) → ∀ e,
      (∑ c ∈ candidates G (pieceLength h),
        ind (component G (toggle G (roundM G z) (roundB' G h z)) c) *
        delta G (roundF G z) (roundM G z) c e) =
          ind (e ∈ roundB' G h z) - ind (e ∈ roundM G z) := by sorry

end
end StochMatchQuery.Union
