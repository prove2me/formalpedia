-- Prove2me | Theorems.Thm_PreprocOWS_Supplement_theorem_9_5
-- name    : PreprocOWS.Supplement.theorem_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:14:01.635858+00:00
-- url     : https://prove2.me/theorems/defb377e-fe2b-462e-8169-5126e7cb046d
-- title:
--   Theorem 9.5 — one-query distinguishing for binary phase states: $\mathbb E_R[\Delta_{\mathcal A}(R)] = O(\sqrt{\log M/K})$
-- statement:
--   Let $R=(R(k,x))_{k\in[K],x\in[N]}$ be independent Rademacher signs. A one-query adversary with workspace dimension $M$ consists of an isometry $V:\mathbb C^N\to\mathbb C^M$ and a projection $\Pi$ on $\mathbb C^M$, both independent of $R$, and a phase function $f_R$ depending arbitrarily on $R$.
--
--   There is a universal constant $C>0$ such that for all $K\ge1$, $N$, $M$ and every such adversary,
--   $$
--   \mathbb E_R\Big[\max_f\Big|\,\mathbb E_k\langle\psi_{R,k}|V^\dagger O_f^\dagger\Pi O_fV|\psi_{R,k}\rangle-\mathbb E_h\langle\psi_h|V^\dagger O_f^\dagger\Pi O_fV|\psi_h\rangle\Big|\Big]\,\le\,C\sqrt{\frac{\log M}{K}},
--   $$
--   where $h$ is a uniform independent sign vector and $|\psi_h\rangle = N^{-1/2}\sum_x h(x)|x\rangle$.
--
--   A single query to an arbitrary phase oracle cannot distinguish a random binary phase state from a fresh one with advantage beyond $O(\sqrt{\log M/K})$.
--
--   Differences from the source:
--   - encoding: O(·) → one constant C > 0 quantified before every parameter and before the adversary; reason: the reading of O(·) used by the published goal Theorem 5.2; the proof supplies explicit constants
--   - encoding: E_R max_f over the arbitrary phase function f → ∀ maps f : Oracle K N → ([M] → Bool) inside E_R; reason: a bound for every map R ↦ f_R is a bound on E_R max_f (finitely many f, so the maximum is attained)
--   - encoding: K keys, bound divided by K → hypothesis 1 ≤ K; reason: excludes only the empty key set, where E_k and the division by K are undefined
--   - encoding: log M inside O(·) → natural logarithm Real.log M; reason: a change of base only rescales the constant of the O(·)
--   - generalization: N = 2^n and workspace dimension M = 2^m (§3, p.11) → any natural numbers N and M; reason: the powers of two are included; the bound is stated for the exact dimensions, and the proof does not use that they are powers of two
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 9.5, p.38 (PDF p.41); Definition 9.4, pp.37–38 (PDF pp.40–41)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Supplement_distAdv
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Theorem 9.5 (One-query distinguishing bound for binary phase states, [LMW24, Theorem 4.17])**,
Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.38 (PDF p.41): for the oracle state distinguishing game associated with the family
`{|ψ_{R,k}⟩}_{k∈[K]}` of Definition 9.4, with `R` a family of independent Rademacher random
variables, every one-query adversary with workspace dimension `M` satisfies
`E_R[Δ_𝒜(R)] ≤ O(√(log M / K))`.

**Formalization Note.** The `O(·)` is one universal `C > 0` chosen before `K, N, M` and the
adversary; `log` is the natural logarithm. The adversary is an isometry `V : ℂ^N → ℂ^M` and a
projection `Π` on `ℂ^M` (Hermitian, idempotent), both independent of `R`, and a phase function
`f R` depending arbitrarily on `R` (`∀` maps `R ↦ f R` encodes `E_R max_f`; the absolute value is
inside the max). `K ≥ 1`. -/
theorem theorem_9_5 : ∃ C : ℝ, 0 < C ∧ ∀ (K N M : ℕ), 1 ≤ K →
    ∀ V : Matrix (Fin M) (Fin N) ℂ, IsIsometry V →
    ∀ P : Matrix (Fin M) (Fin M) ℂ, P.IsHermitian → P * P = P →
    ∀ f : Oracle K N → Fin M → Bool,
      avg (fun R => distAdv V P (f R) R) ≤ C * Real.sqrt (Real.log M / K) := by sorry

end PreprocOWS.Supplement
