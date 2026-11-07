-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_3_1
-- name    : PlantedSubgraphLD.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:28.461113+00:00
-- url     : https://prove2.me/theorems/9eeb0dee-74b2-44a7-ba6c-2ed7dfe162a0
-- title:
--   Lemma 3.1 — $\alpha_n(F)/\beta_n(F)=1+o(1)$ uniformly over $e(F)=o(\sqrt n)$
-- statement:
--   Fix $c>0$, let $\Gamma_n$ be simple graphs with at most $n$ vertices, and let $(d_n)$ be a sequence with $d_n=o(\sqrt n)$. Then, uniformly over all nonempty abstract graphs $F$ (without isolated vertices) with $N_{\Gamma_n}(F)>0$ and $e(F)\le d_n$,
--
--   $$
--   \frac{\alpha_n(F)}{\beta_n(F)}=1+o(1);
--   $$
--
--   that is, for every $\delta>0$, for all sufficiently large $n$ and all such $F$, $|\alpha_n(F)/\beta_n(F)-1|\le\delta$. Consequently, for all sufficiently large $n$ and all such $F$,
--
--   $$
--   \tfrac12\beta_n(F)\le\alpha_n(F)\le2\beta_n(F).\tag{3.7}
--   $$
--
--   This lets the paper replace the exact summands of (3.5) and (3.6) by the simpler $\beta_n(F)$ in the low-degree range.
--
--   Differences from the source:
--   - encoding: a sequence {Γn}n≥1 of simple graphs with at most n vertices → Γ n : SimpleGraph (V n) on a finite type V n with card (V n) ≤ n, for every n : ℕ including n = 0; reason: a sequence indexed from n = 1 extends by the graph on no vertices at n = 0; limits are unchanged
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
--   - encoding: o(·) and 1 + o(1) as n → ∞; log the natural logarithm → Asymptotics.IsLittleO and Filter.Tendsto along Filter.atTop; Real.log; reason: standard rendering of the asymptotic notation
--   - encoding: a sequence dn = o(√n) → d : ℕ → ℝ with d =o[atTop] (n ↦ √n); reason: e(F) ≤ dn depends only on ⌊dn⌋, so real and integer sequences give the same statements
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 3.1, §3.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_alpha
import Definitions.Def_PlantedSubgraphLD_beta

open Filter Asymptotics

namespace PlantedSubgraphLD

/-- **Lemma 3.1.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, Lemma 3.1, p.15 (PDF p.17): "Fix c > 0 and let dn = o(√n).
Uniformly over all nonempty graphs F without isolated vertices such that NΓn(F) > 0 and
e(F) ≤ dn, αn(F)/βn(F) = 1 + o(1). Consequently, for all sufficiently large n,
(1/2)βn(F) ≤ αn(F) ≤ 2βn(F). (3.7)"

**Formalization Note** "Uniformly … = 1 + o(1)" is: for every `δ > 0`, eventually in `n`, every
`F ∈ AbsGraph Γₙ` with `e(F) ≤ dₙ` has `|αₙ(F)/βₙ(F) − 1| ≤ δ`. (3.7) holds eventually, for every
such `F`. `dₙ` is real-valued. Γₙ is on at most `n` vertices (standing assumption, §1.1). -/
theorem lemma_3_1 (c : ℝ) (hc : 0 < c)
    (V : ℕ → Type) [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hV : ∀ n, Fintype.card (V n) ≤ n) (Γ : ∀ n, SimpleGraph (V n))
    (d : ℕ → ℝ) (hd : d =o[atTop] (fun n => Real.sqrt (n : ℝ))) :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ F : AbsGraph (Γ n), (numEdges F : ℝ) ≤ d n →
        |alpha c n F / beta c n F - 1| ≤ δ) ∧
    (∀ᶠ n in atTop, ∀ F : AbsGraph (Γ n), (numEdges F : ℝ) ≤ d n →
        beta c n F / 2 ≤ alpha c n F ∧ alpha c n F ≤ 2 * beta c n F) := by sorry

end PlantedSubgraphLD
