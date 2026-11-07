-- Prove2me | Theorems.Thm_PlantedSubgraphLD_noise_equivalence
-- name    : PlantedSubgraphLD.noise_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:22.963387+00:00
-- url     : https://prove2.me/theorems/c4238b5d-0caa-40f7-80e7-6384d08d9ad4
-- title:
--   §3.2 — $T_\varepsilon$ preserves $G(n,c/n)$, and $T_\varepsilon P_n$ plants the $\varepsilon$-thinned graph
-- statement:
--   Let $c>0$, $\varepsilon\in(0,1)$ and $n>c$, and let $\Gamma$ be a simple graph on a finite vertex set $V$ with $|V|\le n$. Then:
--
--   1. the noise operator preserves the null law, $T_\varepsilon Q_n=Q_n$;
--   2. $T_\varepsilon P_n$ is the law of the union of an independently, uniformly embedded copy of the random subgraph $T_\varepsilon\Gamma$, obtained from $\Gamma$ by deleting each edge independently with probability $\varepsilon$, and an independent $G\sim G(n,c/n)$:
--   $$
--   T_\varepsilon P_n=\sum_{\Gamma'\le\Gamma}(1-\varepsilon)^{e(\Gamma')}\varepsilon^{e(\Gamma)-e(\Gamma')}\,P_n[\Gamma'],
--   $$
--   where $\Gamma'$ runs over the spanning subgraphs of $\Gamma$ and $P_n[\Gamma']$ is the planted law of $\Gamma'$.
--
--   This identifies the paper's definition of the noise (resampling of every pair) with the description used in its computations (thinning of the planted graph).
--
--   Differences from the source:
--   - encoding: graphs on [n] (configurations in {0,1}^{([n] choose 2)}) and laws on them → SimpleGraph (Fin n) and real-valued functions on this finite type; reason: same objects; the probability of an event is a finite sum
--   - encoding: Qn = G(n, c/n), used for n large enough that 0 < c/n < 1 → the published edge-product weight LPCommunity.SBMRecovery.edgeWeight with edge probability c/n clamped into [0, 1], defined for every n; reason: the clamp is the identity for n > c; no statement depends on n ≤ c
--   - encoding: the planted graph Γn, a simple graph with at most n vertices → Γ : SimpleGraph V on a finite type V with card V ≤ n; reason: same instances
--   - encoding: TεPn is the law of the union of an independently embedded copy of TεΓn and an independent sample from G(n, c/n) → the mixture over Γ' ≤ Γ with weights (1 − ε)^{e(Γ')} ε^{e(Γ) − e(Γ')} of the planted laws planted c n Γ'; reason: TεΓn keeps the vertex set of Γn and takes the value Γ' with exactly this probability; given Γ', the embedded union is the planted law of Γ'
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_noisedPlanted

open Classical

namespace PlantedSubgraphLD

/-- **§3.2, noise equivalence.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.2, p.12 (PDF p.14): "Since Tε preserves G(n, c/n),
applying it to Pn leaves the Erdős–Rényi background distributed as G(n, c/n), while each planted
edge survives as a planted edge independently with probability 1 − ε. Equivalently, Tε acts
directly on Γn by deleting each edge independently with probability ε. Writing TεΓn for the
resulting random subgraph, TεPn is the law of the union of an independently embedded copy of
TεΓn and an independent sample from G(n, c/n)."

Two clauses: `T_ε Qₙ = Qₙ`; and `T_ε Pₙ` is the mixture, over the spanning subgraphs
`Γ' ≤ Γ` drawn with the thinning weights `(1 − ε)^{e(Γ')} ε^{e(Γ) − e(Γ')}`, of the planted laws
of `Γ'` (a uniform injective embedding of `Γ'` united with an independent `G(n, c/n)`).

**Formalization Note** `T_εΓ` keeps the vertex set of `Γ`, so `Γ'` ranges over the graphs on
`V` below `Γ`; its law is the product thinning law. -/
theorem noise_equivalence (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : c < n) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V ≤ n) (Γ : SimpleGraph V) :
    noise c ε n (erdosRenyi c n) = erdosRenyi c n ∧
    noisedPlanted c ε n Γ = fun G' =>
      ∑ Γ' ∈ (Finset.univ.filter (fun Γ' : SimpleGraph V => Γ' ≤ Γ)),
        (1 - ε) ^ Γ'.edgeFinset.card * ε ^ (Γ.edgeFinset.card - Γ'.edgeFinset.card) *
          planted c n Γ' G' := by sorry

end PlantedSubgraphLD
