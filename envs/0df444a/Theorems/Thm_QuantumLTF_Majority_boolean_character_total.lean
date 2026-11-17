-- Prove2me | Theorems.Thm_QuantumLTF_Majority_boolean_character_total
-- name    : QuantumLTF.Majority.boolean_character_total
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-16T20:28:07.230204+00:00
-- url     : https://prove2.me/theorems/21d21fd0-b319-455e-a4a6-fee425d22d51
-- title:
--   Total sum of a Boolean character
-- statement:
--   The constant Boolean character sums to the size of the cube, while every nonconstant character cancels:
--
--   $$
--   \sum_{S\subseteq[k]}(-1)^{|T\cap S|}=\begin{cases}2^k,&T=\varnothing,\\0,&T\ne\varnothing.\end{cases}
--   $$
--
--   For nonempty $T$, cancellation is obtained by choosing one coordinate in $T$ and pairing each $S$ with the bit string formed by flipping that coordinate.
-- source:
--   Standard Walsh–Fourier cancellation identity on the Boolean cube.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Majority

open QAlgorithms

theorem boolean_character_total : ∀ k : ℕ, ∀ T : Finset (Fin k), ∑ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) = if T = ∅ then (2 : ℤ)^k else 0 := by sorry

end QuantumLTF.Majority
