-- Prove2me | Theorems.Thm_PoAIndep_Topology_theorem_3_8
-- name    : PoAIndep.Topology.theorem_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:20.714763+00:00
-- url     : https://prove2.me/theorems/3e984194-2302-4354-a161-00c7ec1e48b8
-- title:
--   Theorem 3.8, p. 12 — for any instance with latencies in a standard class 𝓛, ρ(G, r, ℓ) ≤ α(𝓛)
-- statement:
--   Let $\mathcal L$ be a standard class of latency functions with anarchy value $\alpha(\mathcal L)\in[1,\infty]$. Let $(G,r,\ell)$ be any instance — an arbitrary finite directed network with any number of commodities — whose edge latency functions all belong to $\mathcal L$. If $f$ is a feasible flow at Nash equilibrium and $f^*$ is any feasible flow with $C(f^*)>0$, then
--   $$\frac{C(f)}{C(f^*)}\le\alpha(\mathcal L).$$
--   Equivalently, $\rho(G,r,\ell)\le\alpha(\mathcal L)$, where $\rho$ is the ratio between the cost of a Nash flow and of an optimal flow.
--
--   This is the central technical result of the paper: the anarchy value, defined through two-link Pigou-type examples alone, bounds the inefficiency of selfish routing in every network.
--
--   **Formalization Note.** The paper's ratio $\rho(G,r,\ell)$ presupposes that Nash and optimal flows exist and that all Nash flows have the same cost (Proposition 2.4, cited by the paper). The formal statement avoids that dependence: it bounds $C(f)/C(f^*)$ for every feasible Nash flow $f$ and every feasible $f^*$ of positive cost, which, since an optimal flow has the least cost, is the bound on $\rho$. The ratio is compared in $[0,\infty]$.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 12, Theorem 3.8

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem theorem_3_8 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) :
    ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (I : Instance V E),
      InClass I L → ∀ f g : Flow I, IsFlow I f → IsFeasible I f → IsNashFlow I f →
        IsFlow I g → IsFeasible I g → 0 < cost I g →
          ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L := by sorry

end PoAIndep.Topology
