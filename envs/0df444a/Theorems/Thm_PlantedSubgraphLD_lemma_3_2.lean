-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_3_2
-- name    : PlantedSubgraphLD.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:57.741812+00:00
-- url     : https://prove2.me/theorems/7fd8d522-365d-448c-9899-c692ccab7aa4
-- title:
--   Lemma 3.2 — the low-degree condition forces $e(\Gamma_n)=o(\sqrt n)$
-- statement:
--   Fix $c>0$ and let $\Gamma_n$ be simple graphs with at most $n$ vertices. Suppose that $D_n\ge1$ for all sufficiently large $n$ and that (1.3) holds:
--
--   $$
--   \|L_n^{\le D_n}\|^2_{L^2(Q_n)}\to1 .
--   $$
--
--   Then
--
--   1. $e(\Gamma_n)=o(\sqrt n)$;
--   2. the bounds (3.7) hold uniformly over all nonempty abstract graphs $F$ with $N_{\Gamma_n}(F)>0$: for all sufficiently large $n$ and every such $F$, $\tfrac12\beta_n(F)\le\alpha_n(F)\le2\beta_n(F)$.
--
--   The second clause removes the edge range restriction of Lemma 3.1, so that $\alpha_n$ and $\beta_n$ are interchangeable in every sum of the paper.
--
--   Differences from the source:
--   - encoding: graphs on [n] (configurations in {0,1}^{([n] choose 2)}) and laws on them → SimpleGraph (Fin n) and real-valued functions on this finite type; reason: same objects; the probability of an event is a finite sum
--   - encoding: Qn = G(n, c/n), used for n large enough that 0 < c/n < 1 → the published edge-product weight LPCommunity.SBMRecovery.edgeWeight with edge probability c/n clamped into [0, 1], defined for every n; reason: the clamp is the identity for n > c; no statement depends on n ≤ c
--   - encoding: a sequence {Γn}n≥1 of simple graphs with at most n vertices → Γ n : SimpleGraph (V n) on a finite type V n with card (V n) ≤ n, for every n : ℕ including n = 0; reason: a sequence indexed from n = 1 extends by the graph on no vertices at n = 0; limits are unchanged
--   - encoding: ‖L≤D_n‖²_{L²(Qn)}, the squared norm of the orthogonal projection of Ln onto R[X]≤D → lowDegNormSq: the supremum of ⟨Ln, f⟩²_{Qn} / ‖f‖²_{Qn} over f ∈ R[X]≤D with ‖f‖_{Qn} > 0; reason: equal by Cauchy–Schwarz when Qn has full support (n > c), the supremum being attained at the projection; this is the paper's (1.1)
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
--   - encoding: o(·) and 1 + o(1) as n → ∞; log the natural logarithm → Asymptotics.IsLittleO and Filter.Tendsto along Filter.atTop; Real.log; reason: standard rendering of the asymptotic notation
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 3.2, §3.4, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_lowDegNormSq
import Definitions.Def_PlantedSubgraphLD_alpha
import Definitions.Def_PlantedSubgraphLD_beta

open Classical Filter Asymptotics

namespace PlantedSubgraphLD

/-- **Lemma 3.2.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.4, Lemma 3.2, p.16 (PDF p.18): "Suppose that Dn ≥ 1 for all
sufficiently large n and that (1.3) holds. Then e(Γn) = o(√n). Consequently, the bounds in (3.7)
hold uniformly over all nonempty graphs F with NΓn(F) > 0 and no isolated vertices."

**Formalization Note** (1.3) is `lowDegNormSq c n (Γ n) (D n) → 1`. The second clause: eventually
in `n`, every `F ∈ AbsGraph Γₙ` satisfies `βₙ(F)/2 ≤ αₙ(F) ≤ 2βₙ(F)`. -/
theorem lemma_3_2 (c : ℝ) (hc : 0 < c)
    (V : ℕ → Type) [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hV : ∀ n, Fintype.card (V n) ≤ n) (Γ : ∀ n, SimpleGraph (V n))
    (D : ℕ → ℕ) (hD : ∀ᶠ n in atTop, 1 ≤ D n)
    (h13 : Tendsto (fun n => lowDegNormSq c n (Γ n) (D n)) atTop (nhds 1)) :
    (fun n => ((Γ n).edgeFinset.card : ℝ)) =o[atTop] (fun n => Real.sqrt (n : ℝ)) ∧
    (∀ᶠ n in atTop, ∀ F : AbsGraph (Γ n),
        beta c n F / 2 ≤ alpha c n F ∧ alpha c n F ≤ 2 * beta c n F) := by sorry

end PlantedSubgraphLD
