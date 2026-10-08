-- Prove2me | Theorems.Thm_PoAIndep_Topology_theorem_4_2
-- name    : PoAIndep.Topology.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:19.739606+00:00
-- url     : https://prove2.me/theorems/80ff4a41-b5f7-48d1-be8f-07478c3011cd
-- title:
--   Theorem 4.2, p. 14 — for a standard class containing the constants, two-link instances attain the worst Nash/optimal cost ratio over all networks, and it equals α(𝓛)
-- statement:
--   Let $G_2$ be the network with one source vertex, one sink vertex and two edges directed from source to sink. Let $\mathcal L$ be a standard class of latency functions containing the constant functions. If $\mathcal I$ denotes the set of all instances with latency functions in $\mathcal L$ and $\mathcal I_2\subseteq\mathcal I$ the single-commodity instances with underlying network $G_2$, then
--   $$\sup_{(G_2,r,\ell)\in\mathcal I_2}\rho(G_2,r,\ell)=\alpha(\mathcal L)=\sup_{(G,r,\ell)\in\mathcal I}\rho(G,r,\ell).$$
--
--   The statement consists of two parts.
--
--   1. *(Attained on two links.)* For every $b<\alpha(\mathcal L)$ there is a single-commodity instance on $G_2$ with latency functions in $\mathcal L$, a feasible Nash flow $f$ and a feasible flow $f^*$ with $C(f^*)>0$ and $C(f)/C(f^*)>b$.
--   2. *(Upper bound everywhere.)* For every instance on any finite directed network with any number of commodities and latency functions in $\mathcal L$, every feasible Nash flow $f$ and every feasible flow $f^*$ with $C(f^*)>0$ satisfy $C(f)/C(f^*)\le\alpha(\mathcal L)$.
--
--   Part 1 gives $\sup_{\mathcal I_2}\rho\ge\alpha(\mathcal L)$ and part 2 gives $\sup_{\mathcal I}\rho\le\alpha(\mathcal L)$; since instances on $G_2$ are instances of the general model, $\sup_{\mathcal I_2}\rho\le\sup_{\mathcal I}\rho$, and the chain of equalities follows. The price of anarchy for such a class is thus independent of the network topology: the simplest two-link networks are already worst possible.
--
--   **Formalization Note.** The anarchy value and the ratios are compared in $[0,\infty]$, so $\alpha(\mathcal L)=\infty$ is allowed. The paper's $\rho(G,r,\ell)$ presupposes existence of Nash and optimal flows and the uniqueness of the Nash cost (Proposition 2.4, cited); the formal statement uses ratios $C(f)/C(f^*)$ over all feasible Nash flows $f$ and all feasible flows $f^*$ of positive cost instead, which expresses the same suprema without that dependence. $G_2$ is constructed inside the general instance model.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 14, Theorem 4.2

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem theorem_4_2 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (hc : ContainsConstants L) :
    (∀ b : ENNReal, b < anarchyValue L →
      ∃ (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ) (hℓ : ∀ e, IsLatency (ℓ e)),
        InClass (twoLink r hr ℓ hℓ) L ∧
          ∃ f g : Flow (twoLink r hr ℓ hℓ),
            IsFlow _ f ∧ IsFeasible _ f ∧ IsNashFlow _ f ∧
            IsFlow _ g ∧ IsFeasible _ g ∧ 0 < cost _ g ∧
            b < ENNReal.ofReal (cost _ f / cost _ g)) ∧
    (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (I : Instance V E),
      InClass I L → ∀ f g : Flow I, IsFlow I f → IsFeasible I f → IsNashFlow I f →
        IsFlow I g → IsFeasible I g → 0 < cost I g →
          ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L) := by sorry

end PoAIndep.Topology
