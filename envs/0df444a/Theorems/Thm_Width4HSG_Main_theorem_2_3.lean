-- Prove2me | Theorems.Thm_Width4HSG_Main_theorem_2_3
-- name    : Width4HSG.Main.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:23:48.879252+00:00
-- url     : https://prove2.me/theorems/075db7ca-0b92-4fec-9210-44e9aa020c4a
-- title:
--   Theorem 2.3 — expected repair cost under small bias
-- statement:
--   Theorem 2.3 (expected repair cost under small bias). There are absolute constants C_bias, C_edit with the following property. For every n, ℓ, P, F as in Theorem 2.2, there are a choice of interval thresholds θ and deterministic procedures Repair^P_θ : {0, 1}^F → {0, 1}^F, Cost^P_θ : {0, 1}^F → N0, chosen independently of D, such that E_{X∼D}[Cost^P_θ(X)] ≤ C_edit ℓ for every δ-biased distribution D on {0, 1}^F with δ ≤ n^{−C_bias ℓ}. For every candidate x ∈ {0, 1}^F, they satisfy P(Repair^P_θ(x)) = 1, d_H(x, Repair^P_θ(x)) ≤ Cost^P_θ(x), and all fixed transition choices remain unchanged.
--
--   The absolute constants precede n, ℓ and P. Both procedures precede D; their acceptance and edit guarantees hold for every candidate, including candidates outside the support of D.
--
--   Differences from the source:
--   - encoding: uniform distributions and expectations on Boolean words → finite Boolean functions, PMF laws and normalized finite sums; reason: these are the same finite sample spaces and probability laws
--   - encoding: fixed transition positions and free-coordinate inputs → LiveProgram with ordered optional read positions and inputs on its free-coordinate subtype; reason: fixed layers read no input; repairs cannot change fixed choices; suffix averages over unused prefix bits cancel
--   - encoding: checkpoints and collisions of live states → strictly increasing cuts including both endpoints; each available-map collision counted once per position; reason: includes fixed collisions and excludes merges into rejection
--   - encoding: there are thresholds θ and procedures Repair_θ, Cost_θ → existentially chosen final procedures with the thresholds already selected; reason: θ is internal construction data with no separate guarantee in the statement; the resulting procedures are chosen before every distribution D
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, Theorem 2.3, p. 12, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_Checkpoints
import Definitions.Def_Width4HSG_Main_SmallBias

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

theorem theorem_2_3 :
    ∃ Cbias Cedit : ℝ, 0 < Cbias ∧ 0 < Cedit ∧
      ∀ n ℓ d : ℕ, 4 ≤ n → 1 ≤ ℓ → ℓ ≤ n → d ≤ n+1 →
      ∀ P : LiveProgram n d, InCheckpointClass P ℓ → (1/16 : ℝ) ≤ P.density →
      ∃ (repair : (P.free → Bool) → (P.free → Bool)) (cost : (P.free → Bool) → ℕ),
        (∀ x, P.eval (repair x) = true ∧ hamming x (repair x) ≤ cost x) ∧
        ∀ (δ : ℝ) (D : PMF (P.free → Bool)), SmallBias D δ →
          δ ≤ (n : ℝ) ^ (-Cbias * ℓ) →
          expectation D (fun x => (cost x : ℝ)) ≤ Cedit * ℓ
 := by sorry

end Width4HSG.Main
