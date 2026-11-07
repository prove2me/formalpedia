-- Prove2me | Theorems.Thm_QubitFreqSensing_theorem_5_13
-- name    : QubitFreqSensing.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:50.590653+00:00
-- url     : https://prove2.me/theorems/d80b90d5-c49e-4f4b-88d4-8175c4b8070c
-- title:
--   Theorem 5.13 — two $\pm1$ patterns with $\max_b|\int_0^T f_b\cos(\omega_i t)|\ge\gamma T/\sqrt N$ and $O(WT\sqrt N+1)$ sign changes
-- statement:
--   There are universal constants $\gamma>0$ and $C_K>0$ such that the following holds. For every $T>0$, every $N\ge1$ and all $\omega_1,\dots,\omega_N>0$, with $W=\max_i\omega_i$, there are two functions $f_0,f_1:[0,T]\to\{-1,1\}$, each a sign pattern with at most $C_K(WT\sqrt N+1)$ sign changes, such that for every $i$
--
--   $$
--   \max_{b\in\{0,1\}}\left|\int_0^T f_b(t)\cos(\omega_i t)\,dt\right|\ \ge\ \frac{\gamma T}{\sqrt N}. \tag{16}
--   $$
--
--   These two patterns are the controls of Protocol 1: each trial picks one of them uniformly at random and implements it with Pauli $Y$ pulses at its sign changes.
--
--   Differences from the source:
--   - reading: f0 and f1 can be taken to each have at most K = Θ(WT√N + 1) sign changes → each f_b is a sign pattern with m ≤ C_K(WT√N + 1) sign changes, C_K universal and chosen before T, N, ω, held by the same f_0, f_1 as (16); reason: 'can be taken to have at most' is an upper bound; the proof gives 2K − 1 with K = ⌈WT√(2N)/κ⌉
--   - encoding: piecewise-constant f_b : [0, T] → {−1, 1} → IsSignPattern: strict partition, alternating signs on half-open pieces, f_b(T) the last sign; reason: the merged form used by Protocol 1; merging only lowers the count of sign changes
--   - encoding: every finite set ω1, …, ωN > 0, with γT/√N in (16) → N ≥ 1; reason: at N = 0 the bound γT/√N divides by √0 and (16) is vacuous; the page writes √N throughout
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Theorem 5.13, p.23 (PDF p.23)

import Mathlib
import Definitions.Def_QubitFreqSensing_SignPattern

namespace QubitFreqSensing

/-- **Theorem 5.13** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), Theorem 5.13,
p.23). "For every T > 0 and every finite set ω1, . . . , ωN > 0, there exist two piecewise-constant
functions f0, f1 : [0, T] → {−1, 1} such that max_{b∈{0,1}} |∫_0^T fb(t) cos(ωit) dt| ≥ γT/√N
(1 ≤ i ≤ N), (16) where γ > 0 is a universal constant. Moreover, f0 and f1 can be taken to each have
at most K = Θ(WT√N + 1) sign changes, where W = maxi ωi."

**Formalization Note** `γ` and the constant `C_K` of the sign-change bound are universal: they are
chosen before `T`, `N` and `ω`. "Can be taken to have at most `K = Θ(WT√N + 1)` sign changes" is the
upper bound `≤ C_K(WT√N + 1)`, held by the same `f₀, f₁` as (16). `W = max_i ω_i` is `⨆ i, ω i`. -/
theorem theorem_5_13 :
    ∃ γ : ℝ, 0 < γ ∧ ∃ CK : ℝ, 0 < CK ∧
      ∀ T : ℝ, 0 < T → ∀ (N : ℕ), 1 ≤ N → ∀ ω : Fin N → ℝ, (∀ i, 0 < ω i) →
      ∃ f : Fin 2 → ℝ → ℝ,
        (∀ b, ∃ m : ℕ, (m : ℝ) ≤ CK * ((⨆ i, ω i) * T * Real.sqrt N + 1) ∧
          IsSignPattern T (f b) m) ∧
        ∀ i, ∃ b, γ * T / Real.sqrt N ≤ |∫ t in (0 : ℝ)..T, f b t * Real.cos (ω i * t)| := by sorry

end QubitFreqSensing
