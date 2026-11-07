-- Prove2me | Theorems.Thm_PlantedSubgraphLD_theorem_1_1_supercritical
-- name    : PlantedSubgraphLD.theorem_1_1_supercritical
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:17.609203+00:00
-- url     : https://prove2.me/theorems/155ffe2d-3135-4edc-8182-e6bfe3962b4d
-- title:
--   Theorem 1.1 (Supercritical Regime) — treewidth $o(D_n/\log n)$ and vanishing low-degree advantage imply indistinguishability after noise
-- statement:
--   Fix $c>0$ and let $\{\Gamma_n\}_{n\ge1}$ be a sequence of simple graphs with at most $n$ vertices. Let $Q_n=G(n,c/n)$, let $P_n$ be the law of $G\sim Q_n$ with a uniformly random injective copy of $\Gamma_n$ added, and let $T_\varepsilon$ resample each edge indicator from Bernoulli$(c/n)$ with probability $\varepsilon$. Suppose there is a sequence of positive integers $\{D_n\}_{n\ge1}$ such that
--
--   $$
--   \mathrm{tw}(\Gamma_n)=o\Big(\frac{D_n}{\log n}\Big)\tag{1.2}
--   $$
--
--   and
--
--   $$
--   \|L_n^{\le D_n}\|^2_{L^2(Q_n)}=1+o(1).\tag{1.3}
--   $$
--
--   Then, for every fixed $\varepsilon\in(0,1)$,
--
--   $$
--   \|L_{n,\varepsilon}\|^2_{L^2(Q_n)}=1+o(1)\tag{1.4}
--   $$
--
--   and consequently
--
--   $$
--   \|T_\varepsilon P_n-Q_n\|_{\mathrm{TV}}=o(1),\tag{1.5}
--   $$
--
--   where $L_{n,\varepsilon}=d(T_\varepsilon P_n)/dQ_n$.
--
--   The conclusion is information-theoretic: after any constant amount of noise no test, efficient or not, distinguishes the planted model from the null when the planted graph has treewidth $o(D_n/\log n)$ and the degree-$D_n$ advantage vanishes. Both conclusions are stated.
--
--   **Formalization Note** The sequences are indexed by all $n\in\mathbb N$; logarithms are natural; the low-degree norm is the variational form of `lowDegNormSq`.
--
--   Differences from the source:
--   - encoding: graphs on [n] (configurations in {0,1}^{([n] choose 2)}) and laws on them → SimpleGraph (Fin n) and real-valued functions on this finite type; reason: same objects; the probability of an event is a finite sum
--   - encoding: Qn = G(n, c/n), used for n large enough that 0 < c/n < 1 → the published edge-product weight LPCommunity.SBMRecovery.edgeWeight with edge probability c/n clamped into [0, 1], defined for every n; reason: the clamp is the identity for n > c; no statement depends on n ≤ c
--   - encoding: a sequence {Γn}n≥1 of simple graphs with at most n vertices → Γ n : SimpleGraph (V n) on a finite type V n with card (V n) ≤ n, for every n : ℕ including n = 0; reason: a sequence indexed from n = 1 extends by the graph on no vertices at n = 0; limits are unchanged
--   - encoding: a sequence of positive integers {Dn}n≥1 → D : ℕ → ℕ with 0 < D n for every n : ℕ; reason: the value at n = 0 does not affect any limit
--   - encoding: ‖L≤D_n‖²_{L²(Qn)}, the squared norm of the orthogonal projection of Ln onto R[X]≤D → lowDegNormSq: the supremum of ⟨Ln, f⟩²_{Qn} / ‖f‖²_{Qn} over f ∈ R[X]≤D with ‖f‖_{Qn} > 0; reason: equal by Cauchy–Schwarz when Qn has full support (n > c), the supremum being attained at the projection; this is the paper's (1.1)
--   - encoding: ‖Ln,ε‖²_{L²(Qn)} with Ln,ε = d(TεPn)/dQn → l2NormSq Qn (likelihoodRatio TεPn Qn) = Σ_G Qn(G) (TεPn(G)/Qn(G))²; reason: on a finite space where Qn > 0 (n > c) the Radon–Nikodym derivative is the pointwise ratio
--   - encoding: ‖µ − ν‖TV = sup_A |µ(A) − ν(A)| → tvDist: the supremum over Finsets A of |Σ_{x∈A} µ(x) − Σ_{x∈A} ν(x)|; reason: on a finite set every subset is a Finset
--   - encoding: tw(Γ), the minimum width of a tree decomposition → tw Γ := sInf {w | TreewidthLE Γ w} with the published RobertsonSeymour1986.GM5.TreewidthLE; reason: for a finite graph the set is nonempty and the infimum is attained; same value
--   - encoding: o(·) and 1 + o(1) as n → ∞; log the natural logarithm → Asymptotics.IsLittleO and Filter.Tendsto along Filter.atTop; Real.log; reason: standard rendering of the asymptotic notation
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Theorem 1.1, §1.1, pp.3–4 (PDF pp.5–6)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_noisedPlanted
import Definitions.Def_PlantedSubgraphLD_lowDegNormSq
import Definitions.Def_PlantedSubgraphLD_tvDist
import Definitions.Def_PlantedSubgraphLD_tw

open Filter Asymptotics

namespace PlantedSubgraphLD

/-- **Theorem 1.1 (Supercritical Regime).** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…),
§1.1, Theorem 1.1, pp.3–4 (PDF pp.5–6): "Fix c > 0, and let {Γn}n≥1 be a sequence of simple
graphs with at most n vertices. Suppose there exists a sequence of positive integers {Dn}n≥1 such
that tw(Γn) = o(Dn/ log n) (1.2) and ‖L≤Dn_n‖²_{L²(Qn)} = 1 + o(1). (1.3) Then, for every fixed
ε ∈ (0, 1), ‖Ln,ε‖²_{L²(Qn)} = 1 + o(1). (1.4) Consequently, ‖TεPn − Qn‖TV = o(1). (1.5)"

**Formalization Note** Γₙ is a graph on a finite vertex type `V n` with `card (V n) ≤ n`.
Sequences are indexed by all `n : ℕ` (the `n = 0` term does not affect any limit). `o(·)` is
`IsLittleO` along `atTop` and `1 + o(1)` is convergence to `1`; the logarithm is natural
(§3.1). `‖L_{n,ε}‖²` is `l2NormSq Qₙ (T_εPₙ / Qₙ)`; the low-degree norm is the variational
form of `lowDegNormSq`; `T_ε` is the resampling operator (`noisedPlanted`). -/
theorem theorem_1_1_supercritical (c : ℝ) (hc : 0 < c)
    (V : ℕ → Type) [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hV : ∀ n, Fintype.card (V n) ≤ n) (Γ : ∀ n, SimpleGraph (V n))
    (D : ℕ → ℕ) (hD : ∀ n, 0 < D n)
    (h12 : (fun n => (tw (Γ n) : ℝ)) =o[atTop] (fun n => (D n : ℝ) / Real.log (n : ℝ)))
    (h13 : Tendsto (fun n => lowDegNormSq c n (Γ n) (D n)) atTop (nhds 1)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => l2NormSq (erdosRenyi c n)
        (likelihoodRatio (noisedPlanted c ε n (Γ n)) (erdosRenyi c n))) atTop (nhds 1) ∧
      Tendsto (fun n => tvDist (noisedPlanted c ε n (Γ n)) (erdosRenyi c n)) atTop (nhds 0) := by sorry

end PlantedSubgraphLD
