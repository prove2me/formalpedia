-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_4_6
-- name    : PlantedSubgraphLD.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:58.686915+00:00
-- url     : https://prove2.me/theorems/c5212ba3-ba2c-4b93-9a7f-45dcc5dadd0f
-- title:
--   Lemma 4.6 — (1.2) and (1.3) imply $\theta_{n,\varepsilon}=o(1)$
-- statement:
--   Fix $c>0$, let $\Gamma_n$ be simple graphs with at most $n$ vertices and $D_n$ positive integers, and suppose that
--
--   $$
--   \mathrm{tw}(\Gamma_n)=o\Big(\frac{D_n}{\log n}\Big)\quad(1.2)\qquad\text{and}\qquad\|L_n^{\le D_n}\|^2_{L^2(Q_n)}=1+o(1)\quad(1.3).
--   $$
--
--   Then, for every fixed $\varepsilon\in(0,1)$, $\theta_{n,\varepsilon}=o(1)$.
--
--   This is the core estimate of the paper: the connected subgraphs beyond the low-degree range are cut into pieces in that range, and the noise factor $(1-\varepsilon)^{2e(F)}$ outweighs the overlap cost $n^{\mathrm{ov}}$.
--
--   Differences from the source:
--   - encoding: graphs on [n] (configurations in {0,1}^{([n] choose 2)}) and laws on them → SimpleGraph (Fin n) and real-valued functions on this finite type; reason: same objects; the probability of an event is a finite sum
--   - encoding: Qn = G(n, c/n), used for n large enough that 0 < c/n < 1 → the published edge-product weight LPCommunity.SBMRecovery.edgeWeight with edge probability c/n clamped into [0, 1], defined for every n; reason: the clamp is the identity for n > c; no statement depends on n ≤ c
--   - encoding: a sequence {Γn}n≥1 of simple graphs with at most n vertices → Γ n : SimpleGraph (V n) on a finite type V n with card (V n) ≤ n, for every n : ℕ including n = 0; reason: a sequence indexed from n = 1 extends by the graph on no vertices at n = 0; limits are unchanged
--   - encoding: a sequence of positive integers {Dn}n≥1 → D : ℕ → ℕ with 0 < D n for every n : ℕ; reason: the value at n = 0 does not affect any limit
--   - encoding: ‖L≤D_n‖²_{L²(Qn)}, the squared norm of the orthogonal projection of Ln onto R[X]≤D → lowDegNormSq: the supremum of ⟨Ln, f⟩²_{Qn} / ‖f‖²_{Qn} over f ∈ R[X]≤D with ‖f‖_{Qn} > 0; reason: equal by Cauchy–Schwarz when Qn has full support (n > c), the supremum being attained at the projection; this is the paper's (1.1)
--   - encoding: tw(Γ), the minimum width of a tree decomposition → tw Γ := sInf {w | TreewidthLE Γ w} with the published RobertsonSeymour1986.GM5.TreewidthLE; reason: for a finite graph the set is nonempty and the infimum is attained; same value
--   - encoding: o(·) and 1 + o(1) as n → ∞; log the natural logarithm → Asymptotics.IsLittleO and Filter.Tendsto along Filter.atTop; Real.log; reason: standard rendering of the asymptotic notation
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 4.6, §4.2, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_theta
import Definitions.Def_PlantedSubgraphLD_lowDegNormSq
import Definitions.Def_PlantedSubgraphLD_tw

open Filter Asymptotics

namespace PlantedSubgraphLD

/-- **Lemma 4.6.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.2, Lemma 4.6, p.21 (PDF p.23): "Suppose that (1.2) and (1.3) hold.
Then, for every fixed ε ∈ (0, 1), θn,ε = o(1)."

**Formalization Note** The setting of Theorem 1.1: `c > 0`, Γₙ on at most `n` vertices, `Dₙ` a
sequence of positive integers, (1.2) `tw(Γₙ) = o(Dₙ / log n)` and (1.3)
`‖L_n^{≤Dₙ}‖² → 1`. -/
theorem lemma_4_6 (c : ℝ) (hc : 0 < c)
    (V : ℕ → Type) [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hV : ∀ n, Fintype.card (V n) ≤ n) (Γ : ∀ n, SimpleGraph (V n))
    (D : ℕ → ℕ) (hD : ∀ n, 0 < D n)
    (h12 : (fun n => (tw (Γ n) : ℝ)) =o[atTop] (fun n => (D n : ℝ) / Real.log (n : ℝ)))
    (h13 : Tendsto (fun n => lowDegNormSq c n (Γ n) (D n)) atTop (nhds 1)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → Tendsto (fun n => theta c ε n (Γ n)) atTop (nhds 0) := by sorry

end PlantedSubgraphLD
