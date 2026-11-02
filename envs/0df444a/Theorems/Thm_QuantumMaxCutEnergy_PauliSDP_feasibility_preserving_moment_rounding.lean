-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_feasibility_preserving_moment_rounding
-- name    : QuantumMaxCutEnergy.PauliSDP.feasibility_preserving_moment_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:48:15.665852+00:00
-- url     : https://prove2.me/theorems/69d7ac6a-979f-44cb-90d1-658ea70771d5
-- title:
--   Feasibility after mixing and rounding Pauli moments
-- statement:
--   Let $L$ be feasible for the level-$k$ Pauli relaxation and let $N$ be its Gram dimension. Mix $L$ with the identity moment assignment $L_0(I)=1$, $L_0(P)=0$ for $P\ne I$, with weight $0<\tau\le1$.
--
--   Suppose $L'(I)=1$ and every moment of support at most $2k$ differs from $(1-\tau)L+\tau L_0$ by at most $\delta\ge0$. If
--
--   $$\delta N\le\frac\tau2,$$
--
--   then $L'$ is feasible and its Gram matrix is positive definite.
-- source:
--   Gribling, Sinjorgo and Sotirov, arXiv:2504.11120v1, Section 2, Eqs. (2.3)–(2.4): https://arxiv.org/html/2504.11120v1#S2 . The quantitative conditioning and perturbation estimates are elementary consequences of the explicitly defined Pauli moment matrix.

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators
open Matrix

theorem QuantumMaxCutEnergy.PauliSDP.feasibility_preserving_moment_rounding {n k : ℕ}
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L)
    (τ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ)
    (hbudget : δ * (Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n k) : ℝ) ≤ τ / 2)
    (L' : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hidentity : L' (QuantumMaxCutEnergy.PauliSDP.identityWord n) = 1)
    (hclose : ∀ P : QuantumMaxCutEnergy.PauliSDP.Word n,
      (QuantumMaxCutEnergy.PauliSDP.support P).card ≤ 2 * k →
      |L' P - ((1 - τ) * L P + τ * (if P = QuantumMaxCutEnergy.PauliSDP.identityWord n then 1 else 0))| ≤ δ) :
    QuantumMaxCutEnergy.PauliSDP.Feasible k L' ∧
      (QuantumMaxCutEnergy.PauliSDP.realGram k L').PosDef := by sorry
