-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_fixed_level_conditioning_certificate
-- name    : QuantumMaxCutEnergy.PauliSDP.fixed_level_conditioning_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:48:11.273493+00:00
-- url     : https://prove2.me/theorems/dd0fd689-f5d6-47a1-a27c-41ad48b8529f
-- title:
--   Polynomial conditioning for the fixed-level Pauli SDP
-- statement:
--   For the level-$k$ Pauli relaxation on $n$ vertices, set $B=(k+1)(4n+1)^k$. The Gram matrix has at most $B$ rows. Every feasible assignment satisfies $|L(P)|\le1$ for words of support at most $2k$, giving the stated polynomial bound on its squared Euclidean norm.
--
--   If $L(I)=1$ and $|L(P)|\le1/(2(B+1))$ for each nonidentity word of support at most $2k$, then its Gram matrix satisfies
--
--   $$x^{\mathsf T}M_k(L)x\ge\tfrac12\|x\|_2^2.$$
--
--   Thus the normalized feasible region has an explicit rational interior neighborhood and polynomial outer bounds for every fixed level.
-- source:
--   Gribling, Sinjorgo and Sotirov, arXiv:2504.11120v1, Section 2, Eqs. (2.3)–(2.4): https://arxiv.org/html/2504.11120v1#S2 . The quantitative conditioning and perturbation estimates are elementary consequences of the explicitly defined Pauli moment matrix.

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators
open Matrix

theorem QuantumMaxCutEnergy.PauliSDP.fixed_level_conditioning_certificate (n k : ℕ) :
    Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n k) ≤ (k + 1) * (4 * n + 1) ^ k ∧
    (∀ L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ,
      QuantumMaxCutEnergy.PauliSDP.Feasible k L →
      (∀ P : QuantumMaxCutEnergy.PauliSDP.Word n,
        (QuantumMaxCutEnergy.PauliSDP.support P).card ≤ 2 * k → -1 ≤ L P ∧ L P ≤ 1) ∧
      (∑ P : QuantumMaxCutEnergy.PauliSDP.Index n (2 * k), (L P.val) ^ 2) ≤
        (((2 * k + 1) * (4 * n + 1) ^ (2 * k) : ℕ) : ℝ)) ∧
    (∀ L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ,
      L (QuantumMaxCutEnergy.PauliSDP.identityWord n) = 1 →
      (∀ P : QuantumMaxCutEnergy.PauliSDP.Word n,
        (QuantumMaxCutEnergy.PauliSDP.support P).card ≤ 2 * k →
        P ≠ QuantumMaxCutEnergy.PauliSDP.identityWord n →
        |L P| ≤ 1 / (2 * ((((k + 1) * (4 * n + 1) ^ k : ℕ) : ℝ) + 1))) →
      QuantumMaxCutEnergy.PauliSDP.Feasible k L ∧
      (QuantumMaxCutEnergy.PauliSDP.realGram k L).PosDef ∧
      ∀ x : QuantumMaxCutEnergy.PauliSDP.Index n k → ℝ,
        (1 / 2 : ℝ) * (∑ P, (x P) ^ 2) ≤
          star x ⬝ᵥ ((QuantumMaxCutEnergy.PauliSDP.realGram k L) *ᵥ x)) := by sorry
