-- Prove2me | Theorems.Thm_PoAIndep_Topology_lemma_4_1
-- name    : PoAIndep.Topology.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:12.596062+00:00
-- url     : https://prove2.me/theorems/7056cfa0-8ddf-4ddd-b746-1b784b4bb424
-- title:
--   Lemma 4.1, p. 13 — for a standard class containing the constants, two-link instances have ρ arbitrarily close to α(𝓛)
-- statement:
--   Let $G_2$ be the network with one source vertex, one sink vertex and two edges directed from source to sink. Let $\mathcal L$ be a standard class of latency functions containing the constant functions $\ell(x)=c$, $c>0$, and let $\alpha(\mathcal L)\in[1,\infty]$ be its anarchy value. Then
--   $$\sup_{(G_2,r,\ell)\in\mathcal I_2}\rho(G_2,r,\ell)\ge\alpha(\mathcal L),$$
--   where $\mathcal I_2$ is the set of single-commodity instances on $G_2$ with latency functions in $\mathcal L$.
--
--   Concretely: for every $b<\alpha(\mathcal L)$ there are a rate $r>0$ and latency functions $\ell_1,\ell_2\in\mathcal L$ on the two edges of $G_2$, a feasible Nash flow $f$ and a feasible flow $f^*$ with $C(f^*)>0$ such that $C(f)/C(f^*)>b$.
--
--   The lemma formalizes the motivating example of §3.1 and is the lower half of Theorem 4.2.
--
--   **Formalization Note.** $G_2$ is built inside the general instance model (two vertices, two parallel edges, one commodity), so it is literally one of the instances Theorem 3.8 speaks about. Exhibiting a feasible $f^*$ (not necessarily optimal) with $C(f)/C(f^*)>b$ is equivalent to $\rho>b$, because an optimal flow has cost at most $C(f^*)$.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 13, Lemma 4.1

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem lemma_4_1 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (hc : ContainsConstants L) :
    ∀ b : ENNReal, b < anarchyValue L →
      ∃ (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ) (hℓ : ∀ e, IsLatency (ℓ e)),
        InClass (twoLink r hr ℓ hℓ) L ∧
          ∃ f g : Flow (twoLink r hr ℓ hℓ),
            IsFlow _ f ∧ IsFeasible _ f ∧ IsNashFlow _ f ∧
            IsFlow _ g ∧ IsFeasible _ g ∧ 0 < cost _ g ∧
            b < ENNReal.ofReal (cost _ f / cost _ g) := by sorry

end PoAIndep.Topology
