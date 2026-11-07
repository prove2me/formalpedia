-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_4_5
-- name    : PlantedSubgraphLD.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:34.547935+00:00
-- url     : https://prove2.me/theorems/dac6aa93-3ee9-43b1-b188-987d246615b7
-- title:
--   Lemma 4.5 — component expansion: $\sum_F(1-\varepsilon)^{2e(F)}\beta_n(F)\le\theta_{n,\varepsilon}/(1-\theta_{n,\varepsilon})$
-- statement:
--   Fix $c>0$ and $\varepsilon\in(0,1)$, and let $\Gamma_n$ be simple graphs with at most $n$ vertices. Suppose that $\theta_{n,\varepsilon}=o(1)$. Then, for all sufficiently large $n$,
--
--   $$
--   \sum_{\substack{F:\,N_{\Gamma_n}(F)>0\\ 1\le e(F)}}(1-\varepsilon)^{2e(F)}\beta_n(F)\le\frac{\theta_{n,\varepsilon}}{1-\theta_{n,\varepsilon}},
--   $$
--
--   and $\theta_{n,\varepsilon}/(1-\theta_{n,\varepsilon})=o(1)$.
--
--   It reduces the noised sum (4.2), over all subgraphs, to the connected sum $\theta_{n,\varepsilon}$.
--
--   Differences from the source:
--   - encoding: a sequence {Γn}n≥1 of simple graphs with at most n vertices → Γ n : SimpleGraph (V n) on a finite type V n with card (V n) ≤ n, for every n : ℕ including n = 0; reason: a sequence indexed from n = 1 extends by the graph on no vertices at n = 0; limits are unchanged
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
--   - encoding: o(·) and 1 + o(1) as n → ∞; log the natural logarithm → Asymptotics.IsLittleO and Filter.Tendsto along Filter.atTop; Real.log; reason: standard rendering of the asymptotic notation
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 4.5, §4.2, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_theta

open Classical Filter

namespace PlantedSubgraphLD

/-- **Lemma 4.5.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.2, Lemma 4.5, p.20 (PDF p.22): "Suppose that θn,ε = o(1). Then,
for all sufficiently large n, Σ_{F: NΓn(F)>0, 1≤e(F)} (1 − ε)^{2e(F)} βn(F) ≤
θn,ε/(1 − θn,ε) = o(1)."

**Formalization Note** `c > 0`, `ε ∈ (0, 1)` fixed and Γₙ on at most `n` vertices (standing
assumptions of §1.1, §3.1). The conclusion has two clauses: the eventual inequality, and
`θ/(1 − θ) → 0`. -/
theorem lemma_4_5 (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (V : ℕ → Type) [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hV : ∀ n, Fintype.card (V n) ≤ n) (Γ : ∀ n, SimpleGraph (V n))
    (hθ : Tendsto (fun n => theta c ε n (Γ n)) atTop (nhds 0)) :
    (∀ᶠ n in atTop,
      ∑ F ∈ (Finset.univ.filter (fun F : AbsGraph (Γ n) => 1 ≤ numEdges F)),
          (1 - ε) ^ (2 * numEdges F) * beta c n F ≤
        theta c ε n (Γ n) / (1 - theta c ε n (Γ n))) ∧
    Tendsto (fun n => theta c ε n (Γ n) / (1 - theta c ε n (Γ n))) atTop (nhds 0) := by sorry

end PlantedSubgraphLD
