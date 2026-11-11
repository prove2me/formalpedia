-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_4
-- name    : StochMatchQuery.Union.claim_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:43.25043+00:00
-- url     : https://prove2.me/theorems/b4cb3610-a01d-463a-8442-b6ece85ece9d
-- title:
--   Claim 3.4 — Tower identity
-- statement:
--   Use the round of §§3.1–3.2 with $D\ge1$, $h\in(0,1)$, $L,\ell,d,t$ as in (3.2), a random graph $F$ of maximum degree at most $D$, and matchings $M,B\subseteq F$. Conditional on $F$, the reference $B$ is independent of $M$. Cuts and both sets of proposal uniforms are independent of these inputs. Candidates, signatures, signed increments and tables are those defined in the round bundle.
--
--   For every candidate $c$ and edge $e$,
--   $$\mathbb E[\lambda_c\Delta_e(c)]=\mathbb E[1_{\mathcal E_c}\Delta_e(c)].$$
--   Here $\mathcal E_c$ means that $c$ is a component of $M\triangle B'$. The increments may be positive, zero or negative. This records the exact conditional-table identity.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.4, PDF/printed p.15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 4; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : RoundInput G) (D : ℕ) (h : ℝ)
    (hD : 1 ≤ D) (hh : 0 < h ∧ h < 1)
    (hd : ∀ z, 0 < prob q.law (fun a => a = z) → maxDegree G z.1 ≤ D) (c : Realization G) (hc : c ∈ candidates G (pieceLength h)) (e : Edge G) :
    mean (RoundInput.baseLaw G q) (fun z => RoundInput.table G q h z c *
      delta G (roundF G z) (roundM G z) c e) =
    mean (RoundInput.baseLaw G q) (fun z =>
      ind (component G (toggle G (roundM G z) (roundB' G h z)) c) *
      delta G (roundF G z) (roundM G z) c e) := by sorry

end
end StochMatchQuery.Union
