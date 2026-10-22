-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_tcount_nonincrease
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.ma_tcount_nonincrease
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:18:40.932434+00:00
-- url     : https://prove2.me/theorems/33d59ef6-7866-4a49-8a65-95cb9b2dcc7c
-- title:
--   Corollary 3.1: T-count nonincrease
-- statement:
--   Let $U$ have an exact single-qubit Clifford+$T$ decomposition containing exactly $n\ge0$ actual $T$ tokens. Then there is a Matsumoto–Amano normal form $M$ for $U$ satisfying
--
--   $$
--   \operatorname{Tcount}(M)\le n.
--   $$
--   Its chronological expansion into $H,S,T,\omega I$ preserves the absolute matrix $U$ and has at most $n$ actual $T$ letters. Clifford factors carry zero $T$ cost.
--
--   This is the normalization nonincrease guarantee underlying $T$-optimality.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 3, Corollary 3.1: T-count nonincrease

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Corollary 3.1, PDF p.3. The premise is an actual decomposition of T-count n;
the conclusion gives a normal form and a chronological word with no more T's. -/
theorem ma_tcount_nonincrease (U : Mat) (n : ℕ)
    (hU : ∃ w : List Input, inputWordMatrix w = U ∧ inputTCount w = n) :
    ∃ M : NormalForm, maValue M = U ∧ normalTCount M ≤ n ∧
      chronologicalValue (normalWord cliffordH cliffordSH M) = U ∧
      letterTCount (normalWord cliffordH cliffordSH M) ≤ n := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
