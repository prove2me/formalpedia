-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_7_9
-- name    : StochMatchQuery.Union.claim_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:12:19.544322+00:00
-- url     : https://prove2.me/theorems/ad7dbf76-6303-4677-b85d-63050a9f3ece
-- title:
--   Claim 7.9 — Union is a matching
-- statement:
--   Use the independent sources and thresholds of §7: $h=\beta=\varepsilon/10$, $J=\lceil1/h\rceil$, and $i<J$ with $W(E_i)\le hW$. The local map is supplied with independent vertex seeds. Where needed, its hypotheses are exactly (7.8)–(7.10), together with measurable matching output contained in $\mathcal G_C$. Define $M_C^0,M_C,A$ by the marking construction, with $A$ as in (7.11), not all vertices unmatched in $M_C$.
--
--   Suppose $M_N$ is a matching contained in $N\cap\mathcal Q$ with all endpoints in $A$. In every outcome,
--   $$(M_C\cap Q)\cup M_N\text{ is a matching contained in }\mathcal Q,\qquad\operatorname{opt}(\mathcal Q)\ge w(M_C\cap Q)+w(M_N).$$
--   This is the pointwise matching and weight comparison used to conclude Theorem 1.1.
--
--   Differences from the source:
--   - generalization: M0C is the output of the algorithm L_{a,h} of Lemma 5.1 run on G_C with vertex randomness ξ → any vertex-seed law ν and map alg on (G_C, ξ) satisfying CrucialGuarantee, i.e. alg(F∩C) ⊆ F∩C is a matching, alg is measurable, and (7.8)–(7.10) hold; reason: the proof uses only these properties of M0C; Lemma 5.1 instantiated as in §7.3 supplies such a map, so the source claim is an instance
--   - generalization: MN is the random matching supplied by Lemma 6.1 in §7.4 → any MN that in every outcome is a matching of edges of N ∩ 𝒬 with both endpoints in A; reason: the proof of Claim 7.9 uses only these properties; the matching of Lemma 6.1 has them, so the source claim is an instance
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 7.9, PDF/printed p.35. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 7 9; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_7_9 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p w : Edge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hp : ∀ e, 0 < p e ∧ p e ≤ 1) (s : Selector G w)
    (eps : ℝ) (heps : 0 < eps ∧ eps < 1) (i : ℕ) (hi : i < bandCount eps)
    (hband : W G p s (band G p s eps i) ≤ accuracy eps * W G p s Finset.univ)
    (ν : VertexLaw V) (alg : Realization G → ((v : V) → ν.carrier v) → Realization G)
    (r : ℕ) (H : CrucialGuarantee G p s ν alg eps i)
    (MN : AssemblySpace G r ν → Realization G)
    (hMN : ∀ z, IsMatching G (MN z) ∧ MN z ⊆ nonCrucial G p s eps i ∩ queriedRealization G s z.1.1 z.1.2 ∧
      ∀ e ∈ MN z, ∀ v, v ∈ (e : Sym2 V) → v ∈ assemblyAvailable G p s ν alg eps i z) :
    ∀ z : AssemblySpace G r ν,
      IsMatching G ((crucialMarked G p s ν alg eps i z ∩ querySet G s z.1.2) ∪ MN z) ∧
      (crucialMarked G p s ν alg eps i z ∩ querySet G s z.1.2) ∪ MN z ⊆ queriedRealization G s z.1.1 z.1.2 ∧
      subsetOpt G w (queriedRealization G s z.1.1 z.1.2) ≥
        weightOf w (crucialMarked G p s ν alg eps i z ∩ querySet G s z.1.2) + weightOf w (MN z) := by sorry

end
end StochMatchQuery.Union
