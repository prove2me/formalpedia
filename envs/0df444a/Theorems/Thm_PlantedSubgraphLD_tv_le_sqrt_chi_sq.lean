-- Prove2me | Theorems.Thm_PlantedSubgraphLD_tv_le_sqrt_chi_sq
-- name    : PlantedSubgraphLD.tv_le_sqrt_chi_sq
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:58.880533+00:00
-- url     : https://prove2.me/theorems/93480147-dc83-4583-b5a9-4ad4edbf3420
-- title:
--   Proof of Theorem 1.1 — $\|T_\varepsilon P_n-Q_n\|_{\mathrm{TV}}=\frac12\mathbb E_{Q_n}|L_{n,\varepsilon}-1|\le\frac12\sqrt{\|L_{n,\varepsilon}\|^2-1}$
-- statement:
--   Let $c>0$, $\varepsilon\in(0,1)$ and $n>c$, and let $\Gamma$ be a simple graph on at most $n$ vertices. Then
--
--   $$
--   \|T_\varepsilon P_n-Q_n\|_{\mathrm{TV}}=\frac12\,\mathbb E_{Q_n}\big|L_{n,\varepsilon}-1\big|\le\frac12\sqrt{\|L_{n,\varepsilon}\|^2_{L^2(Q_n)}-1}.
--   $$
--
--   The identity expresses the total variation distance through the likelihood ratio; the inequality is Cauchy–Schwarz. It turns the second-moment conclusion (1.4) of Theorem 1.1 into the total variation conclusion (1.5).
--
--   Differences from the source:
--   - encoding: graphs on [n] (configurations in {0,1}^{([n] choose 2)}) and laws on them → SimpleGraph (Fin n) and real-valued functions on this finite type; reason: same objects; the probability of an event is a finite sum
--   - encoding: Qn = G(n, c/n), used for n large enough that 0 < c/n < 1 → the published edge-product weight LPCommunity.SBMRecovery.edgeWeight with edge probability c/n clamped into [0, 1], defined for every n; reason: the clamp is the identity for n > c; no statement depends on n ≤ c
--   - encoding: the planted graph Γn, a simple graph with at most n vertices → Γ : SimpleGraph V on a finite type V with card V ≤ n; reason: same instances
--   - encoding: ‖Ln,ε‖²_{L²(Qn)} with Ln,ε = d(TεPn)/dQn → l2NormSq Qn (likelihoodRatio TεPn Qn) = Σ_G Qn(G) (TεPn(G)/Qn(G))²; reason: on a finite space where Qn > 0 (n > c) the Radon–Nikodym derivative is the pointwise ratio
--   - encoding: ‖µ − ν‖TV = sup_A |µ(A) − ν(A)| → tvDist: the supremum over Finsets A of |Σ_{x∈A} µ(x) − Σ_{x∈A} ν(x)|; reason: on a finite set every subset is a Finset
--   - encoding: E_{Qn}|Ln,ε − 1| → Σ_G Qn(G) |TεPn(G)/Qn(G) − 1|; reason: expectation on a finite space
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), proof of Theorem 1.1, §4.2, p.22 (PDF p.24, last display)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_noisedPlanted
import Definitions.Def_PlantedSubgraphLD_l2NormSq
import Definitions.Def_PlantedSubgraphLD_tvDist

namespace PlantedSubgraphLD

/-- **Proof of Theorem 1.1, Cauchy–Schwarz step.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.2, proof of Theorem 1.1, p.22
(PDF p.24, last display): "Finally, the Cauchy–Schwarz inequality gives
‖TεPn − Qn‖TV = (1/2) E_{Qn}|Ln,ε − 1| ≤ (1/2) √(‖Ln,ε‖²_{L²(Qn)} − 1) = o(1)."

Two clauses for every `n > c`, `ε ∈ (0, 1)` and planted graph on at most `n` vertices: the
identity `‖T_εPₙ − Qₙ‖_TV = ½ E_{Qₙ}|L_{n,ε} − 1|` and the bound by `½ √(‖L_{n,ε}‖² − 1)`.

**Formalization Note** The final "= o(1)" is (1.5) of Theorem 1.1 and is not repeated here. -/
theorem tv_le_sqrt_chi_sq (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : c < n) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V ≤ n) (Γ : SimpleGraph V) :
    tvDist (noisedPlanted c ε n Γ) (erdosRenyi c n) =
        (1 / 2) * ∑ G, erdosRenyi c n G *
          |likelihoodRatio (noisedPlanted c ε n Γ) (erdosRenyi c n) G - 1| ∧
    (1 / 2) * ∑ G, erdosRenyi c n G *
          |likelihoodRatio (noisedPlanted c ε n Γ) (erdosRenyi c n) G - 1| ≤
        (1 / 2) * Real.sqrt (l2NormSq (erdosRenyi c n)
          (likelihoodRatio (noisedPlanted c ε n Γ) (erdosRenyi c n)) - 1) := by sorry

end PlantedSubgraphLD
