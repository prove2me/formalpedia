-- Prove2me | Theorems.Thm_PrivLittlestone_corollary_4_2
-- name    : PrivLittlestone.corollary_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:45:33.693025+00:00
-- url     : https://prove2.me/theorems/74ade8de-6e33-4b5d-b841-9e538ac49fe5
-- title:
--   Corollary 4.2 — $M_T \le \min\{T, \frac{C}{\varepsilon}(K^{3/2}\sqrt{m\log(4/\delta)} + K\log\frac{4K(T+1)}{\beta})\}$
-- statement:
--   There is a universal constant $C$ such that, under the accuracy hypotheses and parameter choices of Theorem 4.1, with probability at least $1 - \beta$,
--   $$
--   M_T \le \min\left\{ T,\ \frac{C}{\varepsilon}\Big( K^{3/2}\sqrt{m \log(4/\delta)} + K \log\frac{4K(T+1)}{\beta} \Big) \right\}.
--   $$
--
--   It converts the threshold $2KU$ of Theorem 4.1 into an explicit rate.
--
--   **Formalization Note** $C$ is chosen before every other quantifier (the instance types, the candidate system, $K, m, T, \varepsilon, \delta, \beta$ and the input strategy).
--
--   Differences from the source:
--
--   - generalization: the accuracy hypotheses of Theorem 4.1 on an admissible realizable input family → every input strategy satisfying (A1) and (A2); reason: as in Theorem 4.1
--   - encoding: a universal constant C → ∃ C before all other quantifiers, which may formally depend on the universe levels; reason: Lean universe polymorphism
--   - reading: (A1), (A2) in the paper's words → (A1) for almost every run, on rounds before the fallback; (A2) for almost every history, at every phase start, over the phase's samples, on the continuation with the aggregate held fixed; reason: as in Theorem 4.1
--   - encoding: randomized adaptive inputs, rounds 1, …, T, fresh randomness → deterministic strategies (fixed coins), 0-based rounds, an explicit product coin space; reason: as in Theorem 4.1
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Corollary 4.2, p.9

import Mathlib
import Definitions.Def_PrivLittlestone_continualLearner
import Definitions.Def_PrivLittlestone_IsA1
import Definitions.Def_PrivLittlestone_IsA2
import Definitions.Def_PrivLittlestone_gameMistakes
import Definitions.Def_PrivLittlestone_aP
import Definitions.Def_PrivLittlestone_Uth

universe u v w

namespace PrivLittlestone

/-- **Corollary 4.2 (Quantitative conversion)** (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Corollary
4.2, p.9). There is a universal constant `C` such that, under the accuracy hypotheses and
parameter choices of Theorem 4.1, with probability at least `1 − β`,
`M_T ≤ min{T, (C/ε)(K^{3/2} √(m log(4/δ)) + K log(4K(T + 1)/β))}`.

**Formalization Note** `C` is chosen before every other quantifier (instance types, the system,
`K, m, T, ε, δ, β`, the strategy); formally it may depend on the universe levels. -/
theorem corollary_4_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) (Z : Type v) (U : Type w) (D : ℕ) (B : ℝ) (sys : RankedCandidateSystem Z U D B)
        (K m T : ℕ) (agg : (Fin m → U) → X → Bool) (κ : (X → Bool) → X × Bool → Option Z)
        (gfb : X → Bool) (ε δ β : ℝ), 1 ≤ K → 1 ≤ m → 1 ≤ T → 0 < ε → ε ≤ 1 → 0 < δ →
        δ ≤ 1 / 2 → 0 < β → β ≤ 1 / 2 →
        20 * (Real.log ((sys.C []).card : ℝ) + aP K m T B ε δ * (D : ℝ) + 1) < (K : ℝ) →
        let P : Alg1Spec X Z U D B :=
          { sys := sys, K := K, m := m, T := T, η := etaP K m ε δ, a := aP K m T B ε δ,
            Uth := Uth K m T ε δ β, εa := epsA ε, agg := agg, κ := κ, gfb := gfb }
        ∀ inp : InputStrategy X T, IsA1 P inp → IsA2 P β inp →
          ENNReal.ofReal (1 - β) ≤ (continualLearner P).μ
            {ω | (gameMistakes (continualLearner P) inp ω : ℝ) ≤
              min (T : ℝ) (C / ε * ((K : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt ((m : ℝ) * Real.log (4 / δ)) +
                (K : ℝ) * Real.log (4 * (K : ℝ) * ((T : ℝ) + 1) / β)))} := by sorry

end PrivLittlestone
