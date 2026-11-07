-- Prove2me | Theorems.Thm_PlantedSubgraphLD_eq_3_6
-- name    : PlantedSubgraphLD.eq_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:44.138208+00:00
-- url     : https://prove2.me/theorems/a2becf5d-513f-40bd-b5a1-674cbaeafd14
-- title:
--   (3.6) — exact expansion of the noised second moment $\|L_{n,\varepsilon}\|^2$
-- statement:
--   Let $c>0$, $\varepsilon\in(0,1)$ and $n>c$, and let $\Gamma$ be a simple graph on at most $n$ vertices. For $L_{n,\varepsilon}=d(T_\varepsilon P_n)/dQ_n$,
--
--   $$
--   \|L_{n,\varepsilon}\|^2_{L^2(Q_n)}=1+\sum_{\substack{F:\,N_{\Gamma}(F)>0\\ F\text{ nonempty}}}(1-\varepsilon)^{2e(F)}\Big(\frac{1-c/n}{c/n}\Big)^{e(F)}\frac{N_{\Gamma}(F)^2|\mathrm{Aut}(F)|}{(n)_{v(F)}}=1+\sum_{F}(1-\varepsilon)^{2e(F)}\alpha_n(F).
--   $$
--
--   Compared with (3.5), the noise damps the contribution of a subgraph with $e$ edges by $(1-\varepsilon)^{2e}$ and removes the degree cut-off; Theorem 1.1 is the statement that this sum tends to $0$.
--
--   Differences from the source:
--   - encoding: graphs on [n] (configurations in {0,1}^{([n] choose 2)}) and laws on them → SimpleGraph (Fin n) and real-valued functions on this finite type; reason: same objects; the probability of an event is a finite sum
--   - encoding: Qn = G(n, c/n), used for n large enough that 0 < c/n < 1 → the published edge-product weight LPCommunity.SBMRecovery.edgeWeight with edge probability c/n clamped into [0, 1], defined for every n; reason: the clamp is the identity for n > c; no statement depends on n ≤ c
--   - encoding: the planted graph Γn, a simple graph with at most n vertices → Γ : SimpleGraph V on a finite type V with card V ≤ n; reason: same instances
--   - encoding: ‖Ln,ε‖²_{L²(Qn)} with Ln,ε = d(TεPn)/dQn → l2NormSq Qn (likelihoodRatio TεPn Qn) = Σ_G Qn(G) (TεPn(G)/Qn(G))²; reason: on a finite space where Qn > 0 (n > c) the Radon–Nikodym derivative is the pointwise ratio
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), (3.6), §3.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_noisedPlanted
import Definitions.Def_PlantedSubgraphLD_l2NormSq
import Definitions.Def_PlantedSubgraphLD_alpha

namespace PlantedSubgraphLD

/-- **(3.6), exact noised expansion.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, (3.6), p.15 (PDF p.17): "Consequently, for
Ln,ε := d(TεPn)/dQn, the same calculation as above gives ‖Ln,ε‖²_{L²(Qn)} = 1 +
Σ_{F: NΓn(F)>0, F nonempty} (1 − ε)^{2e(F)} ((1 − c/n)/(c/n))^{e(F)} NΓn(F)²|Aut(F)| /
(n)_{v(F)}."

**Formalization Note** Stated for every `n > c`, every `ε ∈ (0, 1)` and every planted graph on
at most `n` vertices. The sum is over all of `AbsGraph Γ` (the nonempty `F` with
`N_Γ(F) > 0`). -/
theorem eq_3_6 (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : c < n) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V ≤ n) (Γ : SimpleGraph V) :
    l2NormSq (erdosRenyi c n) (likelihoodRatio (noisedPlanted c ε n Γ) (erdosRenyi c n)) =
      1 + ∑ F : AbsGraph Γ, (1 - ε) ^ (2 * numEdges F) * alpha c n F := by sorry

end PlantedSubgraphLD
