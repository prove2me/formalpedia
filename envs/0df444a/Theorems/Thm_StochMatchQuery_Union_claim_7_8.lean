-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_7_8
-- name    : StochMatchQuery.Union.claim_7_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:16.71121+00:00
-- url     : https://prove2.me/theorems/cee63cb8-a29d-4df4-9b5a-1ab5976a58b4
-- title:
--   Claim 7.8 — Crucial matching survives Q
-- statement:
--   Use the independent sources and thresholds of §7: $h=\beta=\varepsilon/10$, $J=\lceil1/h\rceil$, and $i<J$ with $W(E_i)\le hW$. The local map is supplied with independent vertex seeds. Where needed, its hypotheses are exactly (7.8)–(7.10), together with measurable matching output contained in $\mathcal G_C$. Define $M_C^0,M_C,A$ by the marking construction, with $A$ as in (7.11), not all vertices unmatched in $M_C$.
--
--   Take $r=\lceil C_\varepsilon/p\rceil$ with the exact (7.6) constant and nonempty edge set. Then
--   $$\mathbb E[w(M_C\cap Q)]\ge(1-5h)W_C,\qquad M_C\cap Q\subseteq\mathcal Q.$$
--   The containment is pointwise. The sampled query restriction therefore preserves the required crucial weight.
--
--   Differences from the source:
--   - encoding: p is the minimum of the edge probabilities → the edge set is nonempty where its minimum is used; reason: the minimum in the source is undefined for an edgeless graph
--   - generalization: M0C is the output of the algorithm L_{a,h} of Lemma 5.1 run on G_C with vertex randomness ξ → any vertex-seed law ν and map alg on (G_C, ξ) satisfying CrucialGuarantee, i.e. alg(F∩C) ⊆ F∩C is a matching, alg is measurable, and (7.8)–(7.10) hold; reason: the proof uses only these properties of M0C; Lemma 5.1 instantiated as in §7.3 supplies such a map, so the source claim is an instance
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 7.8, PDF/printed p.34. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 7 8; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_7_8 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p w : Edge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hp : ∀ e, 0 < p e ∧ p e ≤ 1) (s : Selector G w)
    (eps : ℝ) (heps : 0 < eps ∧ eps < 1) (i : ℕ) (hi : i < bandCount eps)
    (hband : W G p s (band G p s eps i) ≤ accuracy eps * W G p s Finset.univ)
    (ν : VertexLaw V) (alg : Realization G → ((v : V) → ν.carrier v) → Realization G)
    (r : ℕ) (H : CrucialGuarantee G p s ν alg eps i)
    (hne : (Finset.univ : Realization G).Nonempty)
    (hr : r = ⌈sampleConstant eps / minProbability G p hne⌉₊) :
    mean (assemblyLaw G p r ν eps) (fun z => weightOf w (crucialMarked G p s ν alg eps i z ∩ querySet G s z.1.2)) ≥
      (1-5*accuracy eps)*W G p s (crucial G p s eps i) ∧
    (∀ z : AssemblySpace G r ν, crucialMarked G p s ν alg eps i z ∩ querySet G s z.1.2 ⊆ queriedRealization G s z.1.1 z.1.2) := by sorry

end
end StochMatchQuery.Union
