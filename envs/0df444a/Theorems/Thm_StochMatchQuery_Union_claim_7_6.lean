-- Prove2me | Theorems.Thm_StochMatchQuery_Union_claim_7_6
-- name    : StochMatchQuery.Union.claim_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:10:53.100619+00:00
-- url     : https://prove2.me/theorems/24b7c633-9db1-451b-af2a-0eaa8e225931
-- title:
--   Claim 7.6 — Independence
-- statement:
--   Use the independent sources and thresholds of §7: $h=\beta=\varepsilon/10$, $J=\lceil1/h\rceil$, and $i<J$ with $W(E_i)\le hW$. The local map is supplied with independent vertex seeds. Where needed, its hypotheses are exactly (7.8)–(7.10), together with measurable matching output contained in $\mathcal G_C$. Define $M_C^0,M_C,A$ by the marking construction, with $A$ as in (7.11), not all vertices unmatched in $M_C$.
--
--   The three objects $(\mathcal G_C,\xi,(m_v)_v)$, $\mathcal G_N$, and $(\mathcal G_j)_{j=1}^r$ are mutually independent. Equivalently the first is independent of the pair of the latter two, which are independent. Thus
--   $$f(\mathcal G_C,\xi,(m_v)_v)\perp(Q,\mathcal G_N)$$
--   for every measurable $f$. This includes the joint object $(M_C^0,M_C,A)$, and $Q\perp\mathcal G_N$ as well. These are statements about the one assembly probability space.
--
--   Differences from the source:
--   - encoding: M0C, MC and A are random variables, functions of (G_C, ξ, m) → alg is an arbitrary jointly measurable map, hypothesis Measurable (Function.uncurry alg); reason: a function of the three sources is a random variable only when measurable; the map of Lemma 5.1 is measurable
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Claim 7.6, PDF/printed p.32. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- claim 7 6; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem claim_7_6 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p w : Edge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hp : ∀ e, 0 < p e ∧ p e ≤ 1) (s : Selector G w)
    (eps : ℝ) (heps : 0 < eps ∧ eps < 1) (i : ℕ) (hi : i < bandCount eps)
    (hband : W G p s (band G p s eps i) ≤ accuracy eps * W G p s Finset.univ)
    (ν : VertexLaw V) (alg : Realization G → ((v : V) → ν.carrier v) → Realization G)
    (r : ℕ) (hmeas : Measurable (Function.uncurry alg)) :
    IndepFun (fun z : AssemblySpace G r ν => (z.1.1 ∩ crucial G p s eps i, z.2))
      (fun z => (z.1.1 ∩ nonCrucial G p s eps i, z.1.2)) (assemblyLaw G p r ν eps) ∧
    IndepFun (fun z : AssemblySpace G r ν => z.1.1 ∩ nonCrucial G p s eps i)
      (fun z => z.1.2) (assemblyLaw G p r ν eps) ∧
    (∀ {B : Type} [MeasurableSpace B]
      (f : (Realization G × (((v : V) → ν.carrier v) × (V → Bool))) → B), Measurable f →
      IndepFun (fun z : AssemblySpace G r ν => f (z.1.1 ∩ crucial G p s eps i, z.2))
        (fun z => (querySet G s z.1.2, z.1.1 ∩ nonCrucial G p s eps i)) (assemblyLaw G p r ν eps)) ∧
    IndepFun (fun z : AssemblySpace G r ν => (crucialRaw G p s ν alg eps i z, crucialMarked G p s ν alg eps i z, assemblyAvailable G p s ν alg eps i z))
      (fun z => (querySet G s z.1.2, z.1.1 ∩ nonCrucial G p s eps i)) (assemblyLaw G p r ν eps) ∧
    IndepFun (fun z : AssemblySpace G r ν => querySet G s z.1.2)
      (fun z => z.1.1 ∩ nonCrucial G p s eps i) (assemblyLaw G p r ν eps) := by sorry

end
end StochMatchQuery.Union
