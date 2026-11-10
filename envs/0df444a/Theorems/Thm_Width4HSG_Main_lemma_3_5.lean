-- Prove2me | Theorems.Thm_Width4HSG_Main_lemma_3_5
-- name    : Width4HSG.Main.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:18:09.428861+00:00
-- url     : https://prove2.me/theorems/765cc23a-e4b1-4947-a2eb-317d4f9513d6
-- title:
--   Lemma 3.5 — local uniformity from small bias
-- statement:
--   Lemma 3.5 (local uniformity from small bias). Let D be a δ-biased distribution on {0, 1}^n, and let J ⊆ [n] have m coordinates. Write D_J for its marginal on J, and U_J for the uniform distribution there. Then d_TV(D_J, U_J) ≤ (δ/2)·√(2^m − 1). (3.2) In particular, D is γ-almost k-wise independent for γ = 2^{k/2}δ.
--
--   Both the marginal bound (including the empty marginal) and the bounded-test almost-independence consequence are included.
--
--   Differences from the source:
--   - encoding: uniform distributions and expectations on Boolean words → finite Boolean functions, PMF laws and normalized finite sums; reason: these are the same finite sample spaces and probability laws
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, Lemma 3.5, p. 16, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_SmallBias

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

theorem lemma_3_5 {n : ℕ} (hn : 4 ≤ n) (D : PMF (Bits n)) (δ : ℝ)
    (hD : SmallBias D δ) :
    (∀ J : Finset (Fin n),
      totalVariation (PMF.map (fun x : Bits n => fun i : J => x i.val) D)
        (PMF.uniformOfFintype (J → Bool)) ≤ δ / 2 * Real.sqrt ((2 : ℝ) ^ J.card - 1)) ∧
    ∀ k : ℕ, AlmostKWise D ((2 : ℝ) ^ ((k : ℝ) / 2) * δ) k
 := by sorry

end Width4HSG.Main
