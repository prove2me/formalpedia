-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_10
-- name    : StochMatchQuery.Union.claim_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:13.279814+00:00
-- url     : https://prove2.me/theorems/d3f6632f-9db6-4f6a-8276-40fbd623194d
-- title:
--   Claim 3.10 — Radius
-- statement:
--   Use the round of §§3.1–3.2 with $D\ge1$, $h\in(0,1)$, $L,\ell,d,t$ as in (3.2), a random graph $F$ of maximum degree at most $D$, and matchings $M,B\subseteq F$. Conditional on $F$, the reference $B$ is independent of $M$. Cuts and both sets of proposal uniforms are independent of these inputs. Candidates, signatures, signed increments and tables are those defined in the round bundle.
--
--   If the previous matching has a local computation of radius $R$, the operational next-round map has a local computation of radius at most
--   $$R+4\ell+4.$$
--   The new vertex seeds contain the old seeds and the proposal and correction coins stored at the least-identifier vertex of each candidate. All local answers concern the same global update.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
--   - encoding: finite adaptive local computation with vertex randomness → well-founded decision trees with arbitrary measurable vertex seed spaces and legal sequential inspections; reason: each branch terminates; the next read depends only on earlier answers; present inspected paths determine reachability
--   - encoding: uniform coins stored at the least-identifier candidate vertex → fixed identifiers from a finite enumeration; stored seed coordinates are clamped to [0,1]; reason: clamping is the identity on uniform inputs and provides a total operational extension to arbitrary seeds
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.10, PDF/printed p.19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 10; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_10 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : RoundInput G) (D : ℕ) (h : ℝ)
    (hD : 1 ≤ D) (hh : 0 < h ∧ h < 1)
    (hd : ∀ z, 0 < prob q.law (fun a => a = z) → maxDegree G z.1 ≤ D) (R : ℕ) {α : V → Type}
    [(v : V) → MeasurableSpace (α v)]
    (previous : Realization G → ((v : V) → α v) → Realization G)
    (hloc : ComputesLocally G R (fun F ξ v => incident G (previous F ξ) v)) :
    ComputesLocally G (R + 4*pieceLength h + 4)
      (fun F (ξ : (v : V) → α v × ((Realization G → ℝ) × (Realization G → ℝ))) v =>
        incident G (roundStep G q D h F (previous F (fun v => (ξ v).1))
          (storedCoin G ξ false) (storedCoin G ξ true)) v) := by sorry

end
end StochMatchQuery.Union
