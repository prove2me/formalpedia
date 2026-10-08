-- Prove2me | Theorems.Thm_ResolvingNRM_FRLower_fr_regret_lower_bound
-- name    : ResolvingNRM.FRLower.fr_regret_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:42:22.21554+00:00
-- url     : https://prove2.me/theorems/ff842d05-3732-4523-885d-c8a54b2ca65b
-- title:
--   Proposition 2 — frequent re-solving loses Ω(√T) against hindsight
-- statement:
--   Consider two independent rate-one Poisson customer classes that each consume one unit of a single resource. The initial resource capacity is the positive integer horizon $T$, and their prices satisfy $0<r_2<r_1$. For every choice of optimal DLP solution used by Algorithm 2, there are constants $M>0$ and $T_0\ge1$, depending only on the prices, such that for every $T\ge T_0$,
--
--   $$
--   v^{\mathrm{HO}}(T,T)-v^{\mathrm{FR}}(T,T)\ge M\sqrt T.
--   $$
--
--   Thus frequent re-solving can lose order $\sqrt T$ even though it reoptimizes every period; the benchmark is the expected hindsight optimum.
--
--   **Formalization Note** Proposition 2 states existence of an instance, while its Appendix C.1 proof supplies this explicit two-class family. The assumption $r_2>0$ is the positive-price reading needed for the paper's LP allocation formula; the inequality $r_2<r_1$ is stated on pp. 18 and 32. The threshold and constant are chosen before the LP selector and the horizon. The printed phase proof uses $T\in3\mathbb N$ although the proposition is stated for all sufficiently large horizons; this gap is recorded in the moderation notes.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Proposition 2 p. 18; Appendix C.1 pp. 32–34

import Mathlib
import Definitions.Def_ResolvingNRM_FRLower_Instance

namespace ResolvingNRM.FRLower

/-- Proposition 2 on the explicit two-class instance of Appendix C.1. The positive
constant and horizon threshold may depend on the two prices, but not on the DLP
tie-breaking selector or the horizon. -/
theorem fr_regret_lower_bound (r₁ r₂ : ℝ) (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ M : ℝ, 0 < M ∧ ∃ T₀ : ℕ, 1 ≤ T₀ ∧
      ∀ sel : (Fin 1 → ℝ) → Fin 2 → ℝ,
        IsDLPSelector (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)) sel →
        ∀ T : ℕ, T₀ ≤ T →
          hindsightValue (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)) (T : ℝ)
              (initialCapacity T) -
            frTail (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)) sel T
              (initialCapacity T) ≥ M * Real.sqrt (T : ℝ) := by sorry

end ResolvingNRM.FRLower
