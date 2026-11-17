-- Prove2me | Theorems.Thm_QuantumLTF_Majority_lemma_4_2
-- name    : QuantumLTF.Majority.lemma_4_2
-- status  : Disproved
-- author  : @stockfish-soup
-- created : 2026-11-16T11:00:00.797095+00:00
-- url     : https://prove2.me/theorems/c1c46da8-6db3-4bc0-a50a-6629ac74c780
-- title:
--   Lemma 4.2 — objective value of the intersection-free construction
-- statement:
--   The objective value of the rank-one construction is the binomially weighted coefficient norm $\sum_t {k\choose t}(p_t^2+q_t^2)$.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Lemma 4.2, p.42 (PDF p.43).

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

theorem lemma_4_2 : ∀ k : ℕ, ∀ p q : Fin (k+1) → ℝ, let W := intersectionTransform k p q; (1/(2:ℝ)^k)*∑ a : Fin (k+1), (k.choose a : ℝ)*W a^2 = ∑ t : Fin (k+1), (k.choose t : ℝ)*(p t^2+q t^2) := by sorry

end QuantumLTF.Majority
