-- Prove2me | Theorems.Thm_ParriloTheta_corollary_5_3
-- name    : ParriloTheta.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:30:51.922586+00:00
-- url     : https://prove2.me/theorems/2647c1a1-7263-4022-8658-eb4934e57bb7
-- title:
--   Corollary 5.3 — a critical graph has $\vartheta$-rank $0$ iff it is a disjoint union of $\alpha(G)$ cliques iff $\overline\chi(G)=\alpha(G)$
-- statement:
--   Let $G=(V,E)$ be a critical graph, i.e. every edge $e$ satisfies $\alpha(G\setminus e)=\alpha(G)+1$. Then
--   1. $\vartheta\text{-rank}(G)=0$ if and only if $G$ is the disjoint union of $\alpha(G)$ cliques;
--   2. $\vartheta\text{-rank}(G)=0$ if and only if $\overline\chi(G)=\alpha(G)$,
--
--   where $\overline\chi(G)=\chi(\overline G)$ is the least number of cliques covering $V$.
--
--   **Formalization Note** "Disjoint union of $\alpha(G)$ cliques" is a labelling $f:V\to\{0,\dots,\alpha(G)-1\}$ such that distinct nodes are adjacent exactly when they have the same label. $\overline\chi(G)$ is `(Gᶜ).chromaticNumber` in `ℕ∞`.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) with V = [n] → G : SimpleGraph V on a finite type V; α(G) = G.indepNum; reason: Lean convention; the same graphs up to relabelling
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
--   - encoding: G is the disjoint union of α(G) cliques → ∃ f : V → Fin α(G), ∀ u ≠ v, (G.Adj u v ↔ f u = f v); reason: the same graphs
--   - encoding: χ̄(G) → (Gᶜ).chromaticNumber : ℕ∞; reason: p.4 sets χ̄(G) = χ(Ḡ); same number
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Corollary 5.3, p.12

import Mathlib
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
import Definitions.Def_ParriloTheta_thetaRank

namespace ParriloTheta

open ChvatalPolytopes.Separation

/-- **Corollary 5.3: critical graphs of ϑ-rank 0.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Corollary 5.3, p.12:
"Assume G = (V, E) is a critical graph, i.e., all its edges are critical. Then we have
ϑ-rank(G) = 0 if and only if G is the disjoint union of α(G) cliques. In particular,
ϑ-rank(G) = 0 if and only if χ̄(G) = α(G)."

**Formalization Note.** "Critical" is the published `IsAlphaCritical`. "G is the disjoint union
of α(G) cliques": there is `f : V → Fin α(G)` such that distinct nodes are adjacent exactly when
they have the same label. `χ̄(G)`, the least number of cliques covering `V`, is
`χ(Ḡ)` (p.4: "we also set χ̄(G) = χ(Ḡ)"), i.e. `(Gᶜ).chromaticNumber : ℕ∞`. -/
theorem corollary_5_3 {V : Type*} [Finite V] (G : SimpleGraph V) (hG : IsAlphaCritical G) :
    (thetaRank G = 0 ↔
      ∃ f : V → Fin G.indepNum, ∀ u v, u ≠ v → (G.Adj u v ↔ f u = f v)) ∧
    (thetaRank G = 0 ↔ Gᶜ.chromaticNumber = (G.indepNum : ℕ∞)) := by sorry

end ParriloTheta
