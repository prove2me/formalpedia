-- Prove2me | Theorems.Thm_WeightedMajority_Shattered_theorem_7_2
-- name    : WeightedMajority.Shattered.theorem_7_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:15.154977+00:00
-- url     : https://prove2.me/theorems/f6395556-6d5c-468b-9445-4fed5f33b110
-- title:
--   Theorem 7.2 — strict Kraft-type inequality for deterministic learners
-- statement:
--   Let $\varphi_1,\ldots,\varphi_n:X\to\{0,1\}$ be shattered by their domain, which may be finite or infinite. Let $A$ be any deterministic online learner. For each $i$, let $M_i$ be the largest number of mistakes $A$ can make on a finite trial sequence whose labels agree with $\varphi_i$. If every $M_i$ is finite, then
--
--   $$
--   \sum_{i=1}^{n}2^{-M_i}<2.
--   $$
--
--   This constrains the simultaneous per-target guarantees of every deterministic learner on a domain that realizes all label patterns across the target functions.
--
--   **Formalization Note** A published online-learning definition supplies the predictor, finite trial sequences, and the mistake-bound supremum in $\mathbb N\cup\{\infty\}$. The explicit finiteness hypothesis permits the conversion of each bound to a natural number. The empty-family sum is zero. Indices are zero-based in Lean.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), pp. 244–245, Theorem 7.2; https://doi.org/10.1006/inco.1994.1009

import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Shattered_ShatteredByDomain

namespace WeightedMajority.Shattered

/-- Littlestone--Warmuth, Theorem 7.2, pp. 244--245. -/
theorem theorem_7_2 {X : Type*} {n : ℕ} (φ : Fin n → X → Bool)
    (hφ : ShatteredByDomain φ) (A : UnderstandingML.OnlineAlg X Bool)
    (hfin : ∀ i, UnderstandingML.mistakeBound A ({φ i} : Set (X → Bool)) < ⊤) :
    (∑ i : Fin n, (2 : ℝ) ^ (-((UnderstandingML.mistakeBound A
      ({φ i} : Set (X → Bool))).toNat : ℤ))) < 2 := by sorry

end WeightedMajority.Shattered
