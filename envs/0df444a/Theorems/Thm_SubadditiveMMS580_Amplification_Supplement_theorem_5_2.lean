-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_theorem_5_2
-- name    : SubadditiveMMS580.Amplification.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:59:08.761225+00:00
-- url     : https://prove2.me/theorems/bd460f47-50d5-41dd-8140-6a9810defcd0
-- title:
--   Theorem 5.2 — reservation theorem: if every agent always has a choice satisfying (18), all targets $\beta_i$ can be met
-- statement:
--   Let $r\ge1$ agents have monotone valuations $v_1,\dots,v_r$ on a finite set $M$ of goods, with targets $\beta_i>0$. Each agent $i$ has a finite collection $\mathcal C_i$ of choices $(H_i,\tilde v_i,\tau_i)$ for $(v_i,\beta_i)$: $H_i\subseteq M$, coefficients $\tilde v_i\ge0$ vanishing on $H_i$, $\tau_i\in\mathbb R$, and condition (16): for every $B\subseteq M\setminus H_i$, $\tilde v_i(B)>\tau_i-\|\tilde v_i\|_\infty$ implies $v_i(H_i\cup B)\ge\beta_i$. The empty choice $(\emptyset,0,0)$ is also allowed.
--
--   Let $Z_1,\dots,Z_r$ (one per agent) and $Z$ be independent mean-one exponential random variables and $R_V(x)=\mathbb E(xZ-V)^+$. For fixed choices of the agents other than $i$ put
--   $$b_g=\sum_{j\ne i}\tilde v_j(g),\qquad V_g=\max_{j\ne i}\tilde v_j(g)Z_j .$$
--   Suppose that for every agent $i$ and every choice of the other agents (each from $\mathcal C_j$ or the empty choice) with pairwise disjoint reserved sets, writing $H=\bigcup_{j\ne i}H_j$, agent $i$ has a choice $(H_i,\tilde v_i,\tau_i)\in\mathcal C_i$ with $H_i\cap H=\emptyset$ and
--   $$\sum_{g\in M\setminus(H\cup H_i)}R_{V_g}(\tilde v_i(g))-\tau_i-\sum_{g\in H_i}b_g>0.\tag{18}$$
--   Then there is an allocation (pairwise disjoint bundles $A_1,\dots,A_r$) with $v_i(A_i)\ge\beta_i$ for every agent $i$.
--
--   This companion theorem coordinates integrally reserved goods with a fractional allocation of the others; it is the engine of the proof of Theorem 1.3 and is not used in the proof of the mission's goal (Theorem 1.1).
--
--   Differences from the source:
--   - generalization: valuations normalized, monotone, with values in ℝ≥0 (§2.1) → real set functions assumed only monotone; reason: the theorem as stated on p. 31 uses only monotonicity; every source instance satisfies the Lean hypotheses
--   - encoding: one probability space carrying Z, Z_1, …, Z_r → for each agent i, the product space of Z and Z_j (j ≠ i) under independent mean-one exponential laws; reason: R_{V_g}(x) depends only on the joint law of Z and the Z_j, j ≠ i, which is the same
--   - encoding: agent i's choice from her collection (the empty choice is allowed) → agent i's choice from C_i; reason: the empty choice makes the left side of (18) equal to 0, so it can never satisfy (18)
--   - encoding: a finite collection of choices → a set of Choice m with Set.Finite; reason: same notion
--   - encoding: an allocation → IsAllocation A (pairwise disjoint bundles, not necessarily covering M); reason: the source allocates leftover goods arbitrarily; by monotonicity this cannot lower any value
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Theorem 5.2, p. 32 (PDF p. 32)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Reservation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation

open MultiAllocToAlloc.Subadditive MeasureTheory

namespace SubadditiveMMS580.Amplification.Supplement

/-- Theorem 5.2 (Reservation theorem; Li–Sun, STOC 2027 submission #580, p. 32), in the setting of
p. 31: `r ≥ 1` agents with monotone valuations `v_i` on `M = Fin m` and targets `β_i > 0`; each
agent has a finite collection `C_i` of choices `(H, ṽ, τ)` for `(v_i, β_i)` (nonnegative
coefficients supported outside `H`, condition (16)), and the empty choice `(∅, 0, 0)` is also
allowed. Suppose that for every agent `i` and every choice `c_j ∈ C_j ∪ {(∅,0,0)}` of the other
agents with pairwise disjoint reserved sets, with `H = ⋃_{j ≠ i} H_j`,
`b_g = ∑_{j ≠ i} ṽ_j(g)` and `V_g = max_{j ≠ i} ṽ_j(g) Z_j`, agent `i` has a choice
`(H_i, ṽ_i, τ_i) ∈ C_i` with `H_i ∩ H = ∅` and
`∑_{g ∈ M \ (H ∪ H_i)} R_{V_g}(ṽ_i(g)) − τ_i − ∑_{g ∈ H_i} b_g > 0` (18). Then there is an
allocation giving every agent `i` value at least `β_i`. -/
theorem theorem_5_2 {m r : ℕ} (hr : 1 ≤ r) (v : Fin r → Finset (Fin m) → ℝ)
    (hmono : ∀ i, IsMonotone (v i)) (β : Fin r → ℝ) (hβ : ∀ i, 0 < β i)
    (C : Fin r → Set (Choice m)) (hfin : ∀ i, (C i).Finite)
    (hC : ∀ i, ∀ c ∈ C i, IsChoice (v i) (β i) c)
    (hyp : ∀ (i : Fin r) (c : Fin r → Choice m),
      (∀ j, j ≠ i → c j ∈ C j ∨ c j = emptyChoice m) →
      (∀ j k, j ≠ i → k ≠ i → j ≠ k → Disjoint (c j).H (c k).H) →
      ∃ ci ∈ C i,
        Disjoint ci.H ((Finset.univ.filter (· ≠ i)).biUnion fun j => (c j).H) ∧
        0 < ∑ g ∈ Finset.univ \ (((Finset.univ.filter (· ≠ i)).biUnion fun j => (c j).H) ∪ ci.H),
              expComparison (fun j : {j : Fin r // j ≠ i} => (c j).coef g) (ci.coef g)
            - ci.τ - ∑ g ∈ ci.H, ∑ j ∈ Finset.univ.filter (· ≠ i), (c j).coef g) :
    ∃ A : Fin r → Finset (Fin m), IsAllocation A ∧ ∀ i : Fin r, β i ≤ v i (A i) := by sorry

end SubadditiveMMS580.Amplification.Supplement
