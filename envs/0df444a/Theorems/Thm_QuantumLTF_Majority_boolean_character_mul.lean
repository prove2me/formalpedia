-- Prove2me | Theorems.Thm_QuantumLTF_Majority_boolean_character_mul
-- name    : QuantumLTF.Majority.boolean_character_mul
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-16T20:28:09.844193+00:00
-- url     : https://prove2.me/theorems/eb26147a-81a4-4bc3-be8c-c6af5a41ecb3
-- title:
--   Multiplication of Boolean characters
-- statement:
--   Let $\chi_T(S)=(-1)^{|T\cap S|}$ be the Boolean character indexed by $T\subseteq[k]$. Character multiplication corresponds to symmetric difference:
--
--   $$
--   \chi_T(S)\chi_U(S)=\chi_{T\triangle U}(S).
--   $$
--
--   This is the pointwise group law for Walsh characters and converts a product of two characters into a single character.
-- source:
--   Standard Walsh–Fourier character multiplication law on the Boolean cube.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Majority

open QAlgorithms
open scoped symmDiff

theorem boolean_character_mul : ∀ k : ℕ, ∀ T U : Finset (Fin k), ∀ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) * (-1 : ℤ) ^ ((U.filter fun i => S i).card) = (-1 : ℤ) ^ (((T ∆ U).filter fun i => S i).card) := by sorry

end QuantumLTF.Majority
