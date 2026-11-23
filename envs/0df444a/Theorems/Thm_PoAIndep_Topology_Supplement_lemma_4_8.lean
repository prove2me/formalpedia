-- Prove2me | Theorems.Thm_PoAIndep_Topology_Supplement_lemma_4_8
-- name    : PoAIndep.Topology.Supplement.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:11:42.862999+00:00
-- url     : https://prove2.me/theorems/2751f512-e51b-4006-8795-5edb23ba494c
-- title:
--   Lemma 4.8, p. 17 — for a standard inhomogeneous class, single-commodity unions of paths have ρ arbitrarily close to α(𝓛)
-- statement:
--   Let $\mathcal L$ be a standard class of latency functions (Definition 3.1) that is inhomogeneous (Definition 4.7), with anarchy value $\alpha(\mathcal L)\in[1,\infty]$ (Definition 3.3). Let $\mathcal I_u$ be the set of single-commodity instances $(G,r,\ell)$ whose underlying network $G$ is a union of paths from the commodity's source to its sink and whose edge latency functions lie in $\mathcal L$. Then
--
--   $$\sup_{(G,r,\ell)\in\mathcal I_u}\rho(G,r,\ell)\ \ge\ \alpha(\mathcal L).$$
--
--   Here $\rho(G,r,\ell)=C(f)/C(f^*)$ is the ratio between the cost of a Nash flow $f$ and the cost of an optimal flow $f^*$. Concretely: for every $b<\alpha(\mathcal L)$ (any finite $b$ when $\alpha(\mathcal L)=\infty$) there are a single-commodity instance on a union of paths with all latency functions in $\mathcal L$, a feasible Nash flow $f$ and a feasible flow $g$ with $C(g)>0$ such that $C(f)/C(g)>b$.
--
--   Together with the upper bound $\rho\le\alpha(\mathcal L)$ of Theorem 3.8 this gives Theorem 4.9. Unlike Theorem 4.5, only one function of $\mathcal L$ needs to be positive at zero, and the class need not be closed under scaling.
--
--   **Formalization Note** The supremum statement is encoded by witnesses, as in the base mission's Theorem 4.2: since $C(g)\ge C(f^*)$ for every feasible $g$, a witness ratio $C(f)/C(g)>b$ gives $\rho>b$, and conversely a near-optimal $g$ witnesses $\rho>b$. Ratios are compared in $[0,\infty]$, so the case $\alpha(\mathcal L)=\infty$ is covered. The witness network has vertex set $\{0,\dots,n_V-1\}$ and edge set $\{0,\dots,n_E-1\}$ for some $n_V,n_E$, which loses nothing since every finite network can be relabelled so.
--
--   Differences from the source:
--   - encoding: sup over 𝓘_u of ρ(G, r, ℓ) ≥ α(𝓛) → for every b < α(𝓛) in [0, ∞] there are an instance in 𝓘_u, a feasible Nash flow f and a feasible flow g with C(g) > 0 and b < C(f)/C(g); reason: the base mission's convention for ρ (Proposition 2.4 is cited, not proved); C(g) ≥ C(f*) makes the two forms equivalent, and it covers α(𝓛) = ∞
--   - encoding: a network obtained from parallel links by repeated edge subdivisions → a finite multigraph on Fin n_V, Fin n_E with m ≥ 1 simple s–t paths partitioning the edges, internally vertex-disjoint, covering every vertex; reason: the same networks up to relabelling
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 17, Lemma 4.8

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model
import Definitions.Def_PoAIndep_Topology_Supplement_Inhomogeneous
import Definitions.Def_PoAIndep_Topology_Supplement_UnionOfPaths

namespace PoAIndep.Topology.Supplement

open PoAIndep.Topology

theorem lemma_4_8 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (hi : IsInhomogeneous L) :
    ∀ b : ENNReal, b < anarchyValue L →
      ∃ (nV nE : ℕ) (I : Instance (Fin nV) (Fin nE)),
        IsUnionOfPathsInstance I ∧ InClass I L ∧
          ∃ f g : Flow I,
            IsFlow I f ∧ IsFeasible I f ∧ IsNashFlow I f ∧
            IsFlow I g ∧ IsFeasible I g ∧ 0 < cost I g ∧
            b < ENNReal.ofReal (cost I f / cost I g) := by sorry

end PoAIndep.Topology.Supplement
