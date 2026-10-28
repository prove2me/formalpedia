-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_uniqueness
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.ma_uniqueness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:19:42.169647+00:00
-- url     : https://prove2.me/theorems/c4a0303b-c4b2-4ca6-8a52-652dd6da7fe9
-- title:
--   Theorem 4.1: MA uniqueness
-- statement:
--   Consider Matsumoto–Amano data $M,N$, with an optional leading $T$, a list of the two syllable choices, and an operator-valued terminal in $\mathcal C=\langle H,S,\omega I\rangle$. Their exact matrix evaluation is injective:
--
--   $$
--   \operatorname{eval}(M)=\operatorname{eval}(N)\quad\Longrightarrow\quad M=N.
--   $$
--   Thus distinct normal forms represent different absolute single-qubit operators. This uniqueness identifies terminal matrices, not distinct spellings for the same Clifford operator.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 3, Theorem 4.1: MA uniqueness

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Theorem 4.1, PDF p.3 (proof p.5). Distinct MA data denote different absolute
U(2) matrices; terminal Clifford operators are already identified extensionally. -/
theorem ma_uniqueness : Function.Injective maValue := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
