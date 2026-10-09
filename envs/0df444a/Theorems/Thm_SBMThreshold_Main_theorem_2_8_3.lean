-- Prove2me | Theorems.Thm_SBMThreshold_Main_theorem_2_8_3
-- name    : SBMThreshold.Main.theorem_2_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:12.60335+00:00
-- url     : https://prove2.me/theorems/aebaeefe-bdc4-4753-928f-fef19fd65f9b
-- title:
--   Theorem 2.8 (3), p. 5 — E[Y_{u,v}Y_{u′,v′} | σ_U σ_{U′}] = (1 + n^{−1+o(1)}) E[Y_{u,v} | ·] E[Y_{u′,v′} | ·]
-- statement:
--   Under the hypotheses of Theorem 2.8, for every sequence $e_n\to0$ there is a sequence $c_n\to0$ such that, for all $n$, all distinct vertices $u,v,u',v'$, all vertex sets $U\ni u,v$ and $U'\ni u',v'$ with $|U|,|U'|\le n^{e_n}$, and all labellings $\tau$, writing $\mathbb E_\tau[\cdot]=\mathbb E[\cdot\mid\sigma_{U\cup U'}=\tau_{U\cup U'}]$,
--   $$
--   \bigl|\mathbb E_\tau[Y_{u,v}Y_{u',v'}]-\mathbb E_\tau[Y_{u,v}]\,\mathbb E_\tau[Y_{u',v'}]\bigr|\le n^{-1+c_n}\,\bigl|\mathbb E_\tau[Y_{u,v}]\,\mathbb E_\tau[Y_{u',v'}]\bigr|.
--   $$
--
--   The path sums for disjoint pairs of vertices are asymptotically uncorrelated, which is what lets the algorithm combine many of them.
--
--   **Formalization Note** Conditioning on $\sigma_U$ and $\sigma_{U'}$ jointly is conditioning on the labels of $U\cup U'$; a single labelling $\tau$ guarantees the two prescriptions agree on $U\cap U'$. The uniformity convention is that of Theorem 2.8 (1).
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 5, Theorem 2.8, display (3)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

/-- Theorem 2.8 (3) (p. 5): uniformly over distinct `u, v, u', v'`, sets `U ⊇ {u, v}`,
`U' ⊇ {u', v'}` of size at most `n^{o(1)}` and labellings of `U ∪ U'`,
`E[Y_{u,v} Y_{u',v'} | σ_U, σ_{U'}] = (1 + n^{-1+o(1)}) E[Y_{u,v} | σ_U, σ_{U'}] E[Y_{u',v'} | σ_U, σ_{U'}]`. -/
theorem theorem_2_8_3 (a b : ℕ → ℝ) (ℓ : ℕ → ℕ) (lam α : ℝ)
    (hA : Assumption27 a b ℓ) (hP : Theorem28Params a b lam α) :
    ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) →
      ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧
        ∀ (n : ℕ) (u v u' v' : Fin n) (U U' : Finset (Fin n)) (τ : Fin n → Bool),
          [u, v, u', v'].Nodup → u ∈ U → v ∈ U → u' ∈ U' → v' ∈ U' →
          (U.card : ℝ) ≤ (n : ℝ) ^ (e n) → (U'.card : ℝ) ≤ (n : ℝ) ^ (e n) →
          |condExp n (a n) (b n) (U ∪ U') τ (fun _ G =>
                pathY n (a n) (b n) (pathLen α n) u v G *
                  pathY n (a n) (b n) (pathLen α n) u' v' G) -
              condExp n (a n) (b n) (U ∪ U') τ
                  (fun _ G => pathY n (a n) (b n) (pathLen α n) u v G) *
                condExp n (a n) (b n) (U ∪ U') τ
                  (fun _ G => pathY n (a n) (b n) (pathLen α n) u' v' G)| ≤
            (n : ℝ) ^ (-1 + c n) *
              |condExp n (a n) (b n) (U ∪ U') τ
                  (fun _ G => pathY n (a n) (b n) (pathLen α n) u v G) *
                condExp n (a n) (b n) (U ∪ U') τ
                  (fun _ G => pathY n (a n) (b n) (pathLen α n) u' v' G)| := by sorry

end SBMThreshold.Main
