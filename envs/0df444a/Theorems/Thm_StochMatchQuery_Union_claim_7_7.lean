-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_7_7
-- name    : StochMatchQuery.Union.claim_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:08.097682+00:00
-- url     : https://prove2.me/theorems/e534572b-45de-4162-b3d9-502e483bd4ec
-- title:
--   Claim 7.7 — Properties of the crucial part
-- statement:
--   Use the independent sources and thresholds of §7: $h=\beta=\varepsilon/10$, $J=\lceil1/h\rceil$, and $i<J$ with $W(E_i)\le hW$. The local map is supplied with independent vertex seeds. Where needed, its hypotheses are exactly (7.8)–(7.10), together with measurable matching output contained in $\mathcal G_C$. Define $M_C^0,M_C,A$ by the marking construction, with $A$ as in (7.11), not all vertices unmatched in $M_C$.
--
--   With $I_v=1_{\{v\in A\}}$, $\pi_v=\Pr(v\in A)$ and $\pi_{uv}=\Pr(u,v\in A)$, all five bounds hold:
--   $$\mathbb E[w(M_C)]\ge(1-4h)W_C,\quad\pi_v\ge\beta,\quad\pi_{uv}\ge\beta^2\ (u\ne v),\quad\pi_v\ge1-\sum_{e\ni v,e\in C}x_e,\quad\sum_v|\operatorname{Cov}(I_u,I_v)|\le K_i.$$
--   The covariance bound includes the diagonal. These are the marked crucial matching's value, availability and dependence properties.
--
--   Differences from the source:
--   - generalization: M0C is the output of the algorithm L_{a,h} of Lemma 5.1 run on G_C with vertex randomness ξ → any vertex-seed law ν and map alg on (G_C, ξ) satisfying CrucialGuarantee, i.e. alg(F∩C) ⊆ F∩C is a matching, alg is measurable, and (7.8)–(7.10) hold; reason: the proof uses only these properties of M0C; Lemma 5.1 instantiated as in §7.3 supplies such a map, so the source claim is an instance
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 7.7, PDF/printed p.33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 7 7; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_7_7 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p w : Edge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hp : ∀ e, 0 < p e ∧ p e ≤ 1) (s : Selector G w)
    (eps : ℝ) (heps : 0 < eps ∧ eps < 1) (i : ℕ) (hi : i < bandCount eps)
    (hband : W G p s (band G p s eps i) ≤ accuracy eps * W G p s Finset.univ)
    (ν : VertexLaw V) (alg : Realization G → ((v : V) → ν.carrier v) → Realization G)
    (r : ℕ) (H : CrucialGuarantee G p s ν alg eps i) :
    mean (assemblyLaw G p r ν eps) (fun z => weightOf w (crucialMarked G p s ν alg eps i z)) ≥
      (1-4*accuracy eps)*W G p s (crucial G p s eps i) ∧
    (∀ v, availability (assemblyLaw G p r ν eps) (assemblyAvailable G p s ν alg eps i) v ≥ accuracy eps) ∧
    (∀ u v, u ≠ v → prob (assemblyLaw G p r ν eps) (fun z => u ∈ assemblyAvailable G p s ν alg eps i z ∧ v ∈ assemblyAvailable G p s ν alg eps i z) ≥ (accuracy eps)^2) ∧
    (∀ v, availability (assemblyLaw G p r ν eps) (assemblyAvailable G p s ν alg eps i) v ≥
      1-∑ e ∈ incident G (crucial G p s eps i) v, marginal G p s e) ∧
    (∀ u, ∑ v : V, |cov (assemblyLaw G p r ν eps) (fun z => ind (u ∈ assemblyAvailable G p s ν alg eps i z))
      (fun z => ind (v ∈ assemblyAvailable G p s ν alg eps i z))| ≤ thresholdK eps i) := by sorry

end
end StochMatchQuery.Union
