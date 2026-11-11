-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_4_2
-- name    : PottsCIZeroFree.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:28.863115+00:00
-- url     : https://prove2.me/theorems/ceefd680-4912-497a-bff9-f0c882dfb18c
-- title:
--   Lemma 4.2 — stationary comparison: $W_{1,d}(\nu_P,\nu_Q)\le C/\kappa$
-- statement:
--   Let $d$ be the shortest-path metric of a finite connected state graph with positive edge lengths, and let $P,Q$ be Markov kernels on its vertex set with stationary laws $\nu_P,\nu_Q$. Suppose $0<\kappa\le1$, $C\ge0$,
--   $$W_{1,d}(P(\xi,\cdot),P(\xi',\cdot))\le(1-\kappa)\,d(\xi,\xi')\quad\text{for adjacent }\xi,\xi',\qquad \mathbb E_{\xi\sim\nu_Q}W_{1,d}(P(\xi,\cdot),Q(\xi,\cdot))\le C .$$
--   Then
--   $$W_{1,d}(\nu_P,\nu_Q)\le C/\kappa .$$
--
--   This converts a one-step contraction of one chain and a one-step closeness of two chains into a distance between their stationary laws.
--
--   **Formalization Note** $d$ is the published path metric `MarkovMixing.pathMetric` with edge lengths $\ell>0$, the same in both directions of an edge; kernels are stochastic matrices and $\nu_P,\nu_Q$ are any stationary distributions.
--
--   Differences from the source:
--   - encoding: positive edge lengths of a graph → ℓ : Ω → Ω → ℝ with ℓ a b > 0 and ℓ a b = ℓ b a on edges; reason: a length per undirected edge; off-edge values are never read by the path metric
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.17 (PDF p.19), Lemma 4.2

import Mathlib
import Definitions.Def_mm_transport

open Classical

namespace PottsCIZeroFree

/-- Lemma 4.2 (Stationary comparison) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.17 (PDF p.19). Let `d` be the
shortest-path metric of a finite connected state graph with positive edge lengths. Let `P, Q`
be Markov kernels on the vertex set of this graph, with stationary laws `ν_P, ν_Q`. Suppose
`0 < κ ≤ 1`, `C ≥ 0`, `W_{1,d}(P(ξ, ·), P(ξ', ·)) ≤ (1 − κ) d(ξ, ξ')` for adjacent `ξ, ξ'`, and
`E_{ξ∼ν_Q} W_{1,d}(P(ξ, ·), Q(ξ, ·)) ≤ C`. Then `W_{1,d}(ν_P, ν_Q) ≤ C/κ`.

**Formalization Note.** `d` is the published `pathMetric Gs ℓ` of a connected graph `Gs` with
edge lengths `ℓ > 0` (the same length in both directions); `W_{1,d}` is `transportDist`.
Kernels are stochastic matrices and `ν_P, ν_Q` are any stationary distributions. -/
theorem lemma_4_2 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (Gs : SimpleGraph Ω)
    (hconn : Gs.Connected) (ℓ : Ω → Ω → ℝ) (hℓ : ∀ a b, Gs.Adj a b → 0 < ℓ a b)
    (hℓs : ∀ a b, Gs.Adj a b → ℓ a b = ℓ b a) (P Q : Matrix Ω Ω ℝ)
    (hP : MarkovMixing.IsStochastic P) (hQ : MarkovMixing.IsStochastic Q) (νP νQ : Ω → ℝ)
    (hνP : MarkovMixing.IsStationary P νP) (hνQ : MarkovMixing.IsStationary Q νQ) (κ C : ℝ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hC : 0 ≤ C)
    (hcontr : ∀ ξ ξ', Gs.Adj ξ ξ' →
      MarkovMixing.transportDist (MarkovMixing.pathMetric Gs ℓ) (P ξ) (P ξ') ≤
        (1 - κ) * MarkovMixing.pathMetric Gs ℓ ξ ξ')
    (hclose : ∑ ξ, νQ ξ * MarkovMixing.transportDist (MarkovMixing.pathMetric Gs ℓ) (P ξ) (Q ξ)
      ≤ C) :
    MarkovMixing.transportDist (MarkovMixing.pathMetric Gs ℓ) νP νQ ≤ C / κ := by sorry

end PottsCIZeroFree
