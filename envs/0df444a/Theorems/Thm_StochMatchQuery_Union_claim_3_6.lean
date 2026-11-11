-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_3_6
-- name    : StochMatchQuery.Union.claim_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:39.899172+00:00
-- url     : https://prove2.me/theorems/cc712a0f-0e2d-447e-b29a-b6b0f19011e4
-- title:
--   Claim 3.6 — Selection
-- statement:
--   Use the round of §§3.1–3.2 with $D\ge1$, $h\in(0,1)$, $L,\ell,d,t$ as in (3.2), a random graph $F$ of maximum degree at most $D$, and matchings $M,B\subseteq F$. Conditional on $F$, the reference $B$ is independent of $M$. Cuts and both sets of proposal uniforms are independent of these inputs. Candidates, signatures, signed increments and tables are those defined in the round bundle.
--
--   Conditional on $(F,M)$, the selection rule has all four properties:
--   $$\tfrac12<P_c\le1,\quad S\text{ is pairwise vertex-disjoint},\quad\Pr(c\in S\mid F,M)=t\lambda_c,\quad S\perp(B,\text{cuts})\mid(F,M).$$
--   The correction probability is therefore valid. Conditional equalities hold on positive-probability conditioning fibers, and the disjointness is pointwise for legal proposal inputs. This preserves the common multiplier for every candidate.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
--   - encoding: independent finite random cuts and uniform proposal coins → cuts are computed from independent real uniforms and proposals use exact real thresholds; reason: floor and modulo give the source finite uniform choices; no probabilities are discretized
--   - encoding: conditional equalities and independence → fiber averages equal almost everywhere and independence under normalized positive-mass fibers; reason: conditional expectations are defined only up to null events; zero is assigned to null fibers
--   - generalization: (i) and (ii) conditional on (F, M), i.e. for the outcomes of (F, M) → (i) for every configuration z and (ii) for every outcome with nonnegative proposal uniforms, including null configurations where the tables are 0 by the null-event convention; reason: on every outcome of positive probability these are the source clauses; the source argument (only present candidates whose vertices have degree at most D can have positive λ) applies unchanged off the support
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 3.6, PDF/printed p.17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 3 6; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_3_6 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (q : RoundInput G) (D : ℕ) (h : ℝ)
    (hD : 1 ≤ D) (hh : 0 < h ∧ h < 1)
    (hd : ∀ z, 0 < prob q.law (fun a => a = z) → maxDegree G z.1 ≤ D) :
    (∀ z : RoundBase G, ∀ c ∈ candidates G (pieceLength h),
      1/2 < isolationProbability G (pieceLength h) (conflictBound D h) (RoundInput.table G q h z) c ∧
      isolationProbability G (pieceLength h) (conflictBound D h) (RoundInput.table G q h z) c ≤ 1) ∧
    (∀ z : RoundOutcome G, (∀ c, 0 ≤ z.2.1 c) →
      ∀ c ∈ RoundInput.kept G q D h z, ∀ b ∈ RoundInput.kept G q D h z,
        c ≠ b → Disjoint (vertices G c) (vertices G b)) ∧
    (∀ c ∈ candidates G (pieceLength h), ∀ᵐ z ∂(RoundInput.fullLaw G q),
      fiberMean (RoundInput.fullLaw G q) (fun a => (roundF G a.1, roundM G a.1))
        (fun a => ind (c ∈ RoundInput.kept G q D h a)) z =
      roundRate D h * RoundInput.table G q h z.1 c) ∧
    (∀ fm : Realization G × Realization G,
      0 < prob q.law (fun a => (a.1,a.2.1) = fm) → IndepFun (RoundInput.kept G q D h) (fun z : RoundOutcome G => (roundB G z.1, z.1.2))
        (let μ := (RoundInput.fullLaw G q).restrict {z | (roundF G z.1, roundM G z.1) = fm};
          (μ Set.univ)⁻¹ • μ)) := by sorry

end
end StochMatchQuery.Union
