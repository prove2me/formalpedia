-- Prove2me | Theorems.Thm_PoAIndep_Topology_Supplement_theorem_4_9
-- name    : PoAIndep.Topology.Supplement.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:13:37.604875+00:00
-- url     : https://prove2.me/theorems/93ed06df-de95-4ff5-9217-1c6093d77a55
-- title:
--   Theorem 4.9, p. 17 — for a standard inhomogeneous class, unions of paths attain the worst ratio α(𝓛) over all networks
-- statement:
--   Let $\mathcal L$ be a standard (Definition 3.1) and inhomogeneous (Definition 4.7) class of latency functions, $\mathcal I$ the set of all instances, with any number of commodities, whose latency functions lie in $\mathcal L$, and $\mathcal I_u\subseteq\mathcal I$ the single-commodity instances whose underlying network is a union of paths. Then
--
--   $$\sup_{(G,r,\ell)\in\mathcal I_u}\rho(G,r,\ell)\ =\ \alpha(\mathcal L)\ =\ \sup_{(G,r,\ell)\in\mathcal I}\rho(G,r,\ell).$$
--
--   The statement consists of two parts.
--
--   1. For every $b<\alpha(\mathcal L)$ there are a single-commodity instance on a union of paths with latency functions in $\mathcal L$, a feasible Nash flow $f$ and a feasible flow $g$ with $C(g)>0$ and $C(f)/C(g)>b$.
--   2. For every instance in $\mathcal I$ (any network, any number of commodities), every feasible Nash flow $f$ and every feasible flow $g$ with $C(g)>0$ satisfy $C(f)/C(g)\le\alpha(\mathcal L)$.
--
--   Since $\mathcal I_u\subseteq\mathcal I$, the two parts give both equalities. For standard inhomogeneous classes, such as those of Section 5 that are not diverse, the worst-case inefficiency of selfish routing therefore already occurs in networks of disjoint paths; the hypothesis of inhomogeneity cannot be dropped (Remark 4.10).
--
--   **Formalization Note** Ratios are compared in $[0,\infty]$ with the same convention for $\rho$ as in the base mission's Theorem 4.2, so $\alpha(\mathcal L)=\infty$ is included. The witness network of part 1 has vertex set $\{0,\dots,n_V-1\}$ and edge set $\{0,\dots,n_E-1\}$ for some $n_V,n_E$.
--
--   Differences from the source:
--   - encoding: sup over 𝓘_u of ρ = α(𝓛) = sup over 𝓘 of ρ → part 1 (for every b < α(𝓛) a witness in 𝓘_u with ratio > b) and part 2 (every ratio C(f)/C(g) over 𝓘 with C(g) > 0 is ≤ α(𝓛)); reason: the base mission's convention for ρ; C(g) ≥ C(f*) and 𝓘_u ⊆ 𝓘 make the two parts equivalent to both equalities, including α(𝓛) = ∞
--   - encoding: a network obtained from parallel links by repeated edge subdivisions → a finite multigraph on Fin n_V, Fin n_E with m ≥ 1 simple s–t paths partitioning the edges, internally vertex-disjoint, covering every vertex; reason: the same networks up to relabelling
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 17, Theorem 4.9

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model
import Definitions.Def_PoAIndep_Topology_Supplement_Inhomogeneous
import Definitions.Def_PoAIndep_Topology_Supplement_UnionOfPaths

namespace PoAIndep.Topology.Supplement

open PoAIndep.Topology

theorem theorem_4_9 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (hi : IsInhomogeneous L) :
    (∀ b : ENNReal, b < anarchyValue L →
      ∃ (nV nE : ℕ) (I : Instance (Fin nV) (Fin nE)),
        IsUnionOfPathsInstance I ∧ InClass I L ∧
          ∃ f g : Flow I,
            IsFlow I f ∧ IsFeasible I f ∧ IsNashFlow I f ∧
            IsFlow I g ∧ IsFeasible I g ∧ 0 < cost I g ∧
            b < ENNReal.ofReal (cost I f / cost I g)) ∧
    (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (I : Instance V E),
      InClass I L → ∀ f g : Flow I, IsFlow I f → IsFeasible I f → IsNashFlow I f →
        IsFlow I g → IsFeasible I g → 0 < cost I g →
          ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L) := by sorry

end PoAIndep.Topology.Supplement
