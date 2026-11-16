-- Prove2me | Theorems.Thm_PreprocOWS_Supplement_theorem_10_4
-- name    : PreprocOWS.Supplement.theorem_10_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:15:55.271064+00:00
-- url     : https://prove2.me/theorems/4fbb8c19-2230-4085-a945-13b36fab12d6
-- title:
--   Theorem 10.4 — distinguishing with $T$ post-queries: $\mathbb E_R[\Delta_{\mathcal A}(R)]=O\big(\sqrt{(T^2+(T+1)\log M)/K}\big)$
-- statement:
--   Let $R=(R(k,x))_{k\in[K],x\in[N]}$ be independent Rademacher signs. The adversary applies a fixed isometry $V:\mathbb C^N\to\mathbb C^M$, one arbitrary phase query $O_{f_R}$, then $T$ queries to $R$ through $A_R=(O_RU)^T$, and measures with a fixed projection $\Pi$. Both experiments use the same $R$ for the post-queries.
--
--   There is a universal constant $C>0$ such that for all $K\ge1$, $N$, $M$, $T$ and every such adversary,
--   $$
--   \mathbb E_R\Big[\max_f\Big|\,\mathbb E_k\|\Pi A_RO_fV|\psi_{R,k}\rangle\|^2-\mathbb E_h\|\Pi A_RO_fV|\psi_h\rangle\|^2\Big|\Big]\,\le\,C\sqrt{\frac{T^2+(T+1)\log M}{K}} .
--   $$
--
--   This extends the one-query distinguishing bound of Theorem 9.5 to adversaries with polynomially many later queries to $R$.
--
--   Differences from the source:
--   - generalization: one fixed unitary U between queries and a phase query on a designated query register → distinct unitaries U_1, …, U_T and an arbitrary query map q : [M] → Option([K]×[N]) with O_R|s⟩ = R(q(s))|s⟩; reason: the page's form is the special case of a constant U and q reading the query register; the same convention as the published base Alg
--   - encoding: O(·) → one constant C > 0 quantified before every parameter and before the adversary; reason: the reading of O(·) used by the published goal Theorem 5.2; the proof supplies explicit constants
--   - encoding: E_R max_f over the arbitrary phase function f → ∀ maps f : Oracle K N → ([M] → Bool) inside E_R; reason: a bound for every map R ↦ f_R is a bound on E_R max_f (finitely many f, so the maximum is attained)
--   - encoding: K keys, bound divided by K → hypothesis 1 ≤ K; reason: excludes only the empty key set, where E_k and the division by K are undefined
--   - encoding: log M inside O(·) → natural logarithm Real.log M; reason: a change of base only rescales the constant of the O(·)
--   - generalization: N = 2^n and workspace dimension M = 2^m (§3, p.11) → any natural numbers N and M; reason: the powers of two are included; the bound is stated for the exact dimensions, and the proof does not use that they are powers of two
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 10.4, p.48 (PDF p.51); §10.2, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Supplement_distAdvPost
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Theorem 10.4 (One-query distinguishing bound for binary phase states, with post queries)**,
Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.48 (PDF p.51): for the variant of the oracle state distinguishing game in which the adversary
also makes `T` queries to `R` after the arbitrary phase query, every such adversary with workspace
dimension `M` satisfies `E_R[Δ_𝒜(R)] ≤ O(√((T² + (T+1) log M)/K))`.

**Formalization Note.** The `O(·)` is one universal `C > 0` chosen before `K, N, M, T` and the
adversary; `log` is natural. `V` (isometry), the projection `Π` and the post-query access `Q` are
independent of `R`; `f R` depends arbitrarily on `R`; both experiments use the same `R` for the
post-queries. `K ≥ 1`. -/
theorem theorem_10_4 : ∃ C : ℝ, 0 < C ∧ ∀ (K N M T : ℕ), 1 ≤ K →
    ∀ V : Matrix (Fin M) (Fin N) ℂ, IsIsometry V →
    ∀ P : Matrix (Fin M) (Fin M) ℂ, P.IsHermitian → P * P = P →
    ∀ Q : QAccess K N M T, ∀ f : Oracle K N → Fin M → Bool,
      avg (fun R => distAdvPost V P Q (f R) R) ≤
        C * Real.sqrt (((T : ℝ) ^ 2 + (T + 1) * Real.log M) / K) := by sorry

end PreprocOWS.Supplement
