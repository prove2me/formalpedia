-- Prove2me | Theorems.Thm_PoAIndep_Topology_Supplement_theorem_4_5
-- name    : PoAIndep.Topology.Supplement.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:48:24.629114+00:00
-- url     : https://prove2.me/theorems/3774a415-bac6-4e5b-9a8e-5482ec7505e4
-- title:
--   Theorem 4.5, pp. 15–16 — for a standard diverse class, parallel links attain the worst single-commodity ratio α(𝓛)
-- statement:
--   Let $G_m$ be the network with one source vertex, one sink vertex and $m$ edges directed from source to sink. Let $\mathcal L$ be a standard and diverse class of latency functions. If $\mathcal I$ denotes the set of all single-commodity instances with latency functions in $\mathcal L$ and $\mathcal I_m\subseteq\mathcal I$ the instances with underlying network $G_m$, then
--   $$\sup_{(G,r,\ell)\in\bigcup_m\mathcal I_m}\rho(G,r,\ell)=\alpha(\mathcal L)=\sup_{(G,r,\ell)\in\mathcal I}\rho(G,r,\ell).$$
--
--   The statement consists of two parts.
--
--   1. For every $b<\alpha(\mathcal L)$ there is a single-commodity instance on some $G_m$ with latency functions in $\mathcal L$, a feasible Nash flow $f$ and a feasible flow $f^*$ with $C(f^*)>0$ and $C(f)/C(f^*)>b$.
--   2. For every single-commodity instance with latency functions in $\mathcal L$, every feasible Nash flow $f$ and every feasible flow $f^*$ with $C(f^*)>0$ satisfy $C(f)/C(f^*)\le\alpha(\mathcal L)$.
--
--   Under the weaker hypothesis of diversity, networks of parallel links are worst possible among single-commodity instances.
--
--   **Formalization Note.** As printed, $\mathcal I$ consists of single-commodity instances; part 2 is restricted accordingly. Ratios are compared in $[0,\infty]$, with the same convention for $\rho$ as in Theorem 4.2.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), pp. 15–16, Theorem 4.5

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology.Supplement

theorem theorem_4_5 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (hd : IsDiverse L) :
    (∀ b : ENNReal, b < anarchyValue L →
      ∃ (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 < r) (ℓ : Fin m → ℝ → ℝ)
        (hℓ : ∀ e, IsLatency (ℓ e)),
        InClass (parallelLinks m hm r hr ℓ hℓ) L ∧
          ∃ f g : Flow (parallelLinks m hm r hr ℓ hℓ),
            IsFlow _ f ∧ IsFeasible _ f ∧ IsNashFlow _ f ∧
            IsFlow _ g ∧ IsFeasible _ g ∧ 0 < cost _ g ∧
            b < ENNReal.ofReal (cost _ f / cost _ g)) ∧
    (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (I : Instance V E),
      I.k = 1 → InClass I L → ∀ f g : Flow I, IsFlow I f → IsFeasible I f → IsNashFlow I f →
        IsFlow I g → IsFeasible I g → 0 < cost I g →
          ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L) := by sorry

end PoAIndep.Topology.Supplement
