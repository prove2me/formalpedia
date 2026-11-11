-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_section_10_6_elementary_instance
-- name    : PriceCapacities.LowerBound.section_10_6_elementary_instance
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:24:13.931187+00:00
-- url     : https://prove2.me/theorems/669ad0b9-75a3-4f80-ab40-097bf2341e97
-- title:
--   §10.6 elementary instance — $n=k\lceil1/\varepsilon\rceil\ge k/\varepsilon$ points on which every capacitated $\varepsilon$-coreset has at least $k$ points
-- statement:
--   Let $z\ge1$ and $k\ge2$ be integers and $0<\varepsilon<1/4$. Put $m=\lceil1/\varepsilon\rceil$ and $\tau=(4k)^{-1/z}$. In $\mathbb R^k\oplus\mathbb R^2$ take the centers $a_i=4e_i$ ($e_i$ orthonormal) and around each $a_i$ put $m$ distinct points on the circle of radius $\tau$ in the two new coordinates ($a_i+w_{i,r}$ with $\|w_{i,r}\|=\tau$, $r\mapsto w_{i,r}$ injective). Let $P$ be the resulting unweighted set. Then
--
--   1. $|P|=km$ and $km\ge k/\varepsilon$;
--   2. the query with centers $a_1,\dots,a_k$ and loads $h_i=m$ has input cost $\mathrm{cost}_P(a,h)\le km\tau^z$, and $km\tau^z=m/4$;
--   3. every capacitated $\varepsilon$-coreset $Q$ for $P$ ($k$ centers, exponent $z$) has at least $k$ points of positive weight.
--
--   This is the elementary $\Omega(k)$ instance used in the proof of Theorem 10.1 when the parameter condition does not admit $t=2$.
--
--   Differences from the source:
--
--   - encoding: orthonormal e_1, …, e_k and two new orthogonal coordinates; m distinct circle points of radius τ → EuclideanSpace ℝ (Fin k ⊕ Fin 2); points elemPoint w i r with ‖w i r‖ = τ and w i injective, for every such w; reason: the source allows any m distinct points on each circle
--   - reading: z, k, ε (from the context of Theorem 10.1) → z : ℕ with 1 ≤ z, k ≥ 2, 0 < ε < 1/4; reason: the instance serves Theorem 10.1
--   - reading: 'If a coreset has fewer than k representatives … a contradiction' → every capacitated ε-coreset Q has size Q ≥ k; reason: the conclusion of the argument
--   - encoding: center tuples C ∈ (ℝ^d)^k, loads h ∈ ℝ^k_{≥0} with Σh_i = n, indices 1..k → C : Fin k → ℝ^d (repetitions allowed), h : Fin k → ℝ with h ≥ 0 and Σh = 1(P), 0-based; reason: same objects; Lean index base
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 40, §10.6 (end of the proof of Lemma 10.4)

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
import Definitions.Def_PriceCapacities_LowerBound_ElementaryInstance

namespace PriceCapacities.LowerBound

theorem section_10_6_elementary_instance (z : ℕ) (hz : 1 ≤ z) (k : ℕ) (hk : 2 ≤ k)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
    (w : Fin k → Fin ⌈1 / ε⌉₊ → EuclideanSpace ℝ (Fin 2))
    (hw : ∀ i r, ‖w i r‖ = (4 * k : ℝ) ^ (-(1 / (z : ℝ))))
    (hinj : ∀ i, Function.Injective (w i)) :
    (elemInstance w).card = k * ⌈1 / ε⌉₊ ∧
    (k : ℝ) / ε ≤ ((elemInstance w).card : ℝ) ∧
    capCost (z : ℝ) (unweighted (elemInstance w)) (elemCenter k) (fun _ => (⌈1 / ε⌉₊ : ℝ))
      ≤ (k : ℝ) * ⌈1 / ε⌉₊ * ((4 * k : ℝ) ^ (-(1 / (z : ℝ)))) ^ (z : ℝ) ∧
    (k : ℝ) * ⌈1 / ε⌉₊ * ((4 * k : ℝ) ^ (-(1 / (z : ℝ)))) ^ (z : ℝ) = (⌈1 / ε⌉₊ : ℝ) / 4 ∧
    ∀ Q : WeightedSet (EuclideanSpace ℝ (Fin k ⊕ Fin 2)),
      IsCapacitatedCoreset k (z : ℝ) ε (unweighted (elemInstance w)) Q → k ≤ size Q := by sorry

end PriceCapacities.LowerBound
