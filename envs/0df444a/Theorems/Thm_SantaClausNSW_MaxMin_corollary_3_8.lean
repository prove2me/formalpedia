-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_corollary_3_8
-- name    : SantaClausNSW.MaxMin.corollary_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:35:10.027366+00:00
-- url     : https://prove2.me/theorems/a50f55d5-79d0-41f0-9b33-2490daf91a48
-- title:
--   Corollary 3.8 — for m ≤ 128n², a rounding with the prescribed marginals gives every agent T/κ with probability ≥ 127/128
-- statement:
--   Let $n\ge1$, $m\le128n^2$ and $\kappa=2^{20}\lceil\sqrt n\rceil$, and let a feasible configuration solution with objective value $T$ for normalized monotone subadditive valuations be given. There is a rounding procedure that selects original configurations $S_i$ with their prescribed marginals, $\Pr[S_i=S]=y_{i,S}$, and returns an allocation $A$ such that, with probability at least $127/128$,
--   $$v_i(A_i)\ge\frac{T}{\kappa}\quad\text{for every agent }i.$$
--   If empty configurations are allowed, the value guarantee applies only to agents selecting a nonempty configuration. It is the rounding step of Theorem 3.12.
--
--   Differences from the source:
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - reading: 'There is a rounding procedure that selects … and gives' → there is a joint law of the selected configurations and a feasible allocation with the stated marginals and success probability; reason: the corollary claims no running time; its content is the existence of the rounding's outcome law
--   - reading: two sentences: without empty configurations every agent gets T/κ; with them only agents selecting a nonempty configuration → one statement: masses of positive weight are on ∅ or on sets of value ≥ T, and with probability ≥ 127/128 every agent with S_i ≠ ∅ gets ≥ T/κ; reason: when no empty configuration has positive mass, S_i ≠ ∅ almost surely and the statement is the first sentence
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 24, Corollary 3.8

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Machine
import Definitions.Def_SantaClausNSW_MaxMin_Valuations

namespace SantaClausNSW.MaxMin

/-- **Corollary 3.8** (p. 24). Let `n ≥ 1`, `m ≤ 128 n²`, `κ = 2^20 ⌈√n⌉`, and let `y` be a
feasible configuration solution with objective value `T ≥ 0` for normalized monotone subadditive
valuations, where empty configurations are allowed (every configuration of positive mass is empty
or has value at least `T`). There is a rounding procedure — a law of selected configurations
`(S_i)` and allocations `(A_i)` — with `Pr[S_i = S] = y_{i,S}` for every `i, S` and, with
probability at least `127/128`, `v_i(A_i) ≥ T/κ` for every agent selecting a nonempty
configuration. -/
theorem corollary_3_8 {n m : ℕ} (hn : 0 < n) (hm : m ≤ 128 * n ^ 2)
    (v : Fin n → Finset (Fin m) → ℝ) (hv : ∀ i, IsValuation (v i) ∧ IsSubadditive (v i))
    (y : Fin n → Finset (Fin m) → ℝ) (hy : IsConfigSolution y) (T : ℝ) (hT : 0 ≤ T)
    (hobj : ∀ i S, 0 < y i S → S = ∅ ∨ T ≤ v i S) :
    ∃ μ : PMF ((Fin n → Finset (Fin m)) × (Fin n → Finset (Fin m))),
      (∀ p ∈ μ.support, IsAllocation p.2) ∧
      (∀ (i : Fin n) (S : Finset (Fin m)), probOf μ (fun p => p.1 i = S) = y i S) ∧
      probOf μ (fun p => ∀ i : Fin n, p.1 i ≠ ∅ →
        T / (2 ^ 20 * (⌈Real.sqrt n⌉₊ : ℝ)) ≤ v i (p.2 i)) ≥ 127 / 128 := by sorry

end SantaClausNSW.MaxMin
