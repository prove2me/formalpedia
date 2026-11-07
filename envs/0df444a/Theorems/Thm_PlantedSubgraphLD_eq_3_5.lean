-- Prove2me | Theorems.Thm_PlantedSubgraphLD_eq_3_5
-- name    : PlantedSubgraphLD.eq_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:26.723404+00:00
-- url     : https://prove2.me/theorems/c60f2f4a-7d7d-4e92-a8a2-d579d72d222f
-- title:
--   (3.5) — exact expansion of the low-degree norm
-- statement:
--   Let $c>0$ and $n>c$, let $\Gamma$ be a simple graph on at most $n$ vertices, and let $D\ge0$ be an integer. Then
--
--   $$
--   \|L_n^{\le D}\|^2_{L^2(Q_n)}=1+\sum_{\substack{F:\,N_{\Gamma}(F)>0\\ 1\le e(F)\le D}}\Big(\frac{1-c/n}{c/n}\Big)^{e(F)}\frac{N_{\Gamma}(F)^2|\mathrm{Aut}(F)|}{(n)_{v(F)}}=1+\sum_{\substack{F:\,N_\Gamma(F)>0\\1\le e(F)\le D}}\alpha_n(F),
--   $$
--
--   the sum ranging over the isomorphism classes of nonempty subgraphs of $\Gamma$ with at most $D$ edges. The empty graph contributes the $1$.
--
--   This is the exact form of the low-degree second moment; the hypothesis (1.3) of Theorem 1.1 is a statement about this sum.
--
--   Differences from the source:
--   - encoding: graphs on [n] (configurations in {0,1}^{([n] choose 2)}) and laws on them → SimpleGraph (Fin n) and real-valued functions on this finite type; reason: same objects; the probability of an event is a finite sum
--   - encoding: Qn = G(n, c/n), used for n large enough that 0 < c/n < 1 → the published edge-product weight LPCommunity.SBMRecovery.edgeWeight with edge probability c/n clamped into [0, 1], defined for every n; reason: the clamp is the identity for n > c; no statement depends on n ≤ c
--   - encoding: the planted graph Γn, a simple graph with at most n vertices → Γ : SimpleGraph V on a finite type V with card V ≤ n; reason: same instances
--   - encoding: ‖L≤D_n‖²_{L²(Qn)}, the squared norm of the orthogonal projection of Ln onto R[X]≤D → lowDegNormSq: the supremum of ⟨Ln, f⟩²_{Qn} / ‖f‖²_{Qn} over f ∈ R[X]≤D with ‖f‖_{Qn} > 0; reason: equal by Cauchy–Schwarz when Qn has full support (n > c), the supremum being attained at the projection; this is the paper's (1.1)
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
--   - generalization: the degree Dn of the sequence (a positive integer) → every D : ℕ; reason: §3.3 defines the projection for every integer D ≥ 0 and the derivation of (3.5) does not use D ≥ 1; at D = 0 both sides are 1
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), (3.5), §3.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_lowDegNormSq
import Definitions.Def_PlantedSubgraphLD_alpha

open Classical

namespace PlantedSubgraphLD

/-- **(3.5), exact low-degree expansion.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.3, (3.5), p.15 (PDF p.17):
"‖L≤Dn_n‖²_{L²(Qn)} = 1 + Σ_{F: NΓn(F)>0, 1≤e(F)≤Dn} ((1 − c/n)/(c/n))^{e(F)} NΓn(F)²|Aut(F)| /
(n)_{v(F)}, where the sum ranges over isomorphism classes of nonempty subgraphs of Γn."

**Formalization Note** Stated for every `n > c` (the standing assumption 0 < c/n < 1 of §3.1),
every planted graph on at most `n` vertices and every degree `D ≥ 0` (§3.3: "For an integer
D ≥ 0"). The sum is over `AbsGraph Γ` with `1 ≤ e(F) ≤ D`; the summand is `alpha c n F`. -/
theorem eq_3_5 (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : c < n) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V ≤ n) (Γ : SimpleGraph V) (D : ℕ) :
    lowDegNormSq c n Γ D =
      1 + ∑ F ∈ (Finset.univ.filter (fun F : AbsGraph Γ => 1 ≤ numEdges F ∧ numEdges F ≤ D)),
        alpha c n F := by sorry

end PlantedSubgraphLD
