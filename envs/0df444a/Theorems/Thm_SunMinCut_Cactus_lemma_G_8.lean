-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_G_8
-- name    : SunMinCut.Cactus.lemma_G_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:25:00.340318+00:00
-- url     : https://prove2.me/theorems/788b8a11-1bb3-46cc-99bc-4cd50975fb5f
-- title:
--   Lemma G.8 — coherent interval correspondence
-- statement:
--   Let $G$ be a connected aggregated graph on $n\ge2$ vertices with positive capacities, $K$ a connected loopless cactus on $q\ge2$ vertices, $\pi:V\to V(K)$ a surjection and $r$ the root. Fix any Euler unfolding: an Euler circuit of $K^+$ ($K$ with doubled bridges) from $\pi(r)$ with positions $0,\dots,k$, representatives $\iota$ with $\iota(\pi(r))=0$, $W=\sum_e w_e$, $P=W+1$ and the objective graph $J$. Then
--   1. every coherent nonempty interval $I\subseteq\{1,\dots,k\}$ (one containing all or none of the copies of each cactus vertex) gives a represented cut $\pi^{-1}(\mathrm{occ}(I))$ of $K$ avoiding $r$, and every represented root-avoiding shore arises from exactly one coherent nonempty interval (a bijection);
--   2. a coherent interval has weight in $J$ exactly its original cut weight, and this is at most $W$;
--   3. every other nonempty interval in $\{1,\dots,k\}$ has weight at least $P$ in $J$, and $P>W$.
--
--   Differences from the source:
--   - encoding: "correspond bijectively" → the map I ↦ π⁻¹(occ(I)) lands in the represented root-avoiding shores and each such shore has exactly one coherent preimage; reason: this is the bijection
--   - encoding: "Drop resulting loops" in J → loops kept with their weight; reason: a loop lies in no cut, so no interval weight changes
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma G.8, p. 48

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_CactusGraph
import Definitions.Def_SunMinCut_Cactus_Intervals

namespace SunMinCut.Cactus

/-- **Lemma G.8 (Coherent interval correspondence)**, Sun 2026, doi:10.5281/zenodo.23915020,
p. 48: let `K` be a connected loopless cactus on `q ≥ 2` vertices with a surjection
`π : V(G) → V(K)`, and fix an Euler unfolding from `π(r)` with positions `0, …, k`, objective
graph `J`, `W = Σ_e w_e` and `P = W + 1`. The nonempty intervals in `{1, …, k}` that do not
separate the copies of any cactus vertex correspond bijectively (through `I ↦ π⁻¹(occ(I))`) to the
represented root-avoiding cuts of `K`; they have exactly their original cut weights in `J`, all
at most `W`; every other nonempty interval in `{1, …, k}` has weight at least `P > W` in `J`. -/
theorem lemma_G_8 (n m q e : ℕ) (hn : 2 ≤ n) (G : Graph n m) (hpos : Positive G)
    (hconn : Connected G) (hagg : Aggregated G) (K : MGraph q e) (hK : K.IsCactus) (hq : 2 ≤ q)
    (π : Fin n → Fin q) (hπ : Function.Surjective π) (r : Fin n) (k : ℕ)
    (U : Unfolding K π r k) :
    (∀ a b, 1 ≤ a → a ≤ b → b ≤ k → Coherent U (interval k a b) →
      bip (posShore U.occ π (interval k a b)) ∈ repCuts K π ∧
        r ∉ posShore U.occ π (interval k a b)) ∧
    (∀ S : Finset (Fin n), bip S ∈ repCuts K π → r ∉ S →
      ∃! ab : ℕ × ℕ, 1 ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ k ∧ Coherent U (interval k ab.1 ab.2) ∧
        posShore U.occ π (interval k ab.1 ab.2) = S) ∧
    (∀ a b, 1 ≤ a → a ≤ b → b ≤ k → Coherent U (interval k a b) →
      (objJ G U).uSum ((objJ G U).delta (interval k a b)) =
          cutw G (posShore U.occ π (interval k a b)) ∧
        cutw G (posShore U.occ π (interval k a b)) ≤ totalWeight G) ∧
    (∀ a b, 1 ≤ a → a ≤ b → b ≤ k → ¬ Coherent U (interval k a b) →
      totalWeight G + 1 ≤ (objJ G U).uSum ((objJ G U).delta (interval k a b))) ∧
    totalWeight G < totalWeight G + 1 := by sorry

end SunMinCut.Cactus
