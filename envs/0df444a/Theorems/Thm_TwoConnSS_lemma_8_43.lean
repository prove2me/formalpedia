-- Prove2me | Theorems.Thm_TwoConnSS_lemma_8_43
-- name    : TwoConnSS.lemma_8_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:30.924467+00:00
-- url     : https://prove2.me/theorems/9cb85425-67b3-4951-afe6-4e53dc3df9ae
-- title:
--   Lemma 8.43 — $\mathrm{opt}(G)\ge\max\{n, 5s+\kappa-1\}$
-- statement:
--   Let $G$ be a structured graph on $n$ vertices, and let $S$ be in the final configuration of Algorithm B: one large 2EC component $L$ and 4-cycle components $C_1, \dots, C_s$, each adjacent only to $L$. Let $\kappa$ be the minimum number of components of a selection of artificial edges. Then
--   $$\mathrm{opt}_E(G) \ge \max\{\, n,\; 5s + \kappa - 1 \,\}.$$
--
--   This lower bound, with Lemma 8.44, gives the matroid solution its approximation guarantee (display (30)).
--
--   Differences from the source:
--   - reading: the final configuration of §8.3.4 → `IsFinalConfigB` (canonical for B, one large 2EC component L, every other component a 4-cycle adjacent only to L) with G structured; reason: these are the properties §8.3.4 states for the configuration Algorithm B reaches
--   - encoding: opt(G) ≥ max{n, 5s + κ − 1} → every 2ECSS F has |F| ≥ n and |F| ≥ 5s + κ − 1, in ℤ; reason: avoids an infimum and natural-number subtraction
--   - encoding: κ, the minimum over selections → any κ attained by a selection and at most every selection's component count (`IsKappa`); reason: a minimum with a witness
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Lemma 8.43, p.69 (PDF p.70); configuration §8.3.4, pp.67–68

import Mathlib
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsKappa

namespace TwoConnSS

/-- **Lemma 8.43: a lower bound on the optimum in Algorithm B's final configuration.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Lemma 8.43, p.69: "We have
opt(G) ≥ max{n, 5s + κ − 1}."

Let `G` be structured, and let `S` be in the final configuration of Algorithm B (§8.3.4, p.67):
canonical for B, one large 2EC component `L`, and `s` 4-cycle components each adjacent to no
component other than `L`. Let `κ` be the minimum number of components of a selection of artificial
edges (p.68). Then every 2ECSS `F` of `G` has `|F| ≥ n` and `|F| ≥ 5s + κ − 1`.

**Formalization Note.** `opt(G) ≥ x` is written as "every 2ECSS has at least `x` edges"; the bound
is in `ℤ`. `G` structured is the standing assumption of §8; the proof uses its 3-matching property
(Lemma 7.3). -/
theorem lemma_8_43 (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset (Sym2 V))
    (L : Finset V) (κ : ℕ) (hG : Structured α η G) (hS : IsFinalConfigB G S L)
    (hκ : IsKappa G S L κ) :
    ∀ F, IsTwoECSS G F → Fintype.card V ≤ F.card ∧
      5 * ((cyc4 S).card : ℤ) + (κ : ℤ) - 1 ≤ (F.card : ℤ) := by sorry

end TwoConnSS
