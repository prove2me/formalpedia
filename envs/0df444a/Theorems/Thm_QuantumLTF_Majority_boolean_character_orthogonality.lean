-- Prove2me | Theorems.Thm_QuantumLTF_Majority_boolean_character_orthogonality
-- name    : QuantumLTF.Majority.boolean_character_orthogonality
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-16T20:25:25.343203+00:00
-- url     : https://prove2.me/theorems/d53fa5a4-373a-4806-b01b-8c023a859721
-- title:
--   Orthogonality of Boolean subset characters
-- statement:
--   For a subset $T\subseteq[k]$, define its Boolean character by $\chi_T(S)=(-1)^{|T\cap S|}$. These characters are orthogonal under the unnormalized counting measure on the Boolean cube:
--
--   $$
--   \sum_{S\subseteq[k]}\chi_T(S)\chi_U(S)=2^k\,\mathbf 1_{T=U}.
--   $$
--
--   This is the elementary Fourier-analytic cancellation underlying weighted Krawtchouk orthogonality after characters are grouped by Hamming weight.
-- source:
--   Standard Walsh–Fourier character orthogonality on the Boolean cube; used implicitly in Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Section 4.2 Krawtchouk orthogonality calculation.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Majority

open QAlgorithms

theorem boolean_character_orthogonality : ∀ k : ℕ, ∀ T U : Finset (Fin k), ∑ S : Qubits k, (-1 : ℤ) ^ ((T.filter fun i => S i).card) * (-1 : ℤ) ^ ((U.filter fun i => S i).card) = if T = U then (2 : ℤ)^k else 0 := by sorry

end QuantumLTF.Majority
