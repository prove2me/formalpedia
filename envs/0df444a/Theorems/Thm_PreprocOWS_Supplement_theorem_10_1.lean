-- Prove2me | Theorems.Thm_PreprocOWS_Supplement_theorem_10_1
-- name    : PreprocOWS.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:14:48.721962+00:00
-- url     : https://prove2.me/theorems/a12108cd-7915-4340-96ab-ebe9b2ce45c0
-- title:
--   Theorem 10.1 — search with $T$ post-queries: $\mathbb E_R[\mathrm{Win}]=O\big((T^2+(T+1)\log M)/K\big)$ (corrected: $\log M\to\log(2M)$)
-- statement:
--   Let $R=(R(k,x))_{k\in[K],x\in[N]}$ be independent Rademacher signs. The adversary applies a fixed isometry $V:\mathbb C^N\to\mathbb C^M$, one query to an arbitrary phase oracle $O_{f_R}$ ($f_R$ depends arbitrarily on $R$), then $T$ queries to $R$ through $A_R=(O_RU)^T$, and measures with a fixed projective measurement $\{\Pi_k\}$.
--
--   There is a universal constant $C>0$ such that for all $K\ge1$, $N$, $M$, $T$ and every such adversary,
--   $$
--   \mathbb E_R\Big[\max_f\ \mathbb E_k\big\|\Pi_k\,A_R\,O_f\,V|\psi_{R,k}\rangle\big\|^2\Big]\,\le\,C\,\frac{T^2+(T+1)\log(2M)}{K}.
--   $$
--
--   The one-query search bound of Theorem 9.2 thus survives polynomially many later queries to $R$.
--
--   Differences from the source:
--   - correction: O((T² + (T+1) log M)/K) → C·(T² + (T+1)·log(2M))/K; reason: as printed the bound is 0 at K = N = M = 1, T = 0, where Win = 1 for every adversary; log(2M) is the paper's own form in Theorem 1.3 (p.5, PDF p.8)
--   - generalization: one fixed unitary U between queries and a phase query on a designated query register → distinct unitaries U_1, …, U_T and an arbitrary query map q : [M] → Option([K]×[N]) with O_R|s⟩ = R(q(s))|s⟩; reason: the page's form is the special case of a constant U and q reading the query register; the same convention as the published base Alg
--   - encoding: O(·) → one constant C > 0 quantified before every parameter and before the adversary; reason: the reading of O(·) used by the published goal Theorem 5.2; the proof supplies explicit constants
--   - encoding: E_R max_f over the arbitrary phase function f → ∀ maps f : Oracle K N → ([M] → Bool) inside E_R; reason: a bound for every map R ↦ f_R is a bound on E_R max_f (finitely many f, so the maximum is attained)
--   - encoding: K keys, bound divided by K → hypothesis 1 ≤ K; reason: excludes only the empty key set, where E_k and the division by K are undefined
--   - encoding: log M inside O(·) → natural logarithm Real.log M; reason: a change of base only rescales the constant of the O(·)
--   - generalization: N = 2^n and workspace dimension M = 2^m (§3, p.11) → any natural numbers N and M; reason: the powers of two are included; the bound is stated for the exact dimensions, and the proof does not use that they are powers of two
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 10.1, p.43 (PDF p.46); §10.1.1, p.44 (PDF p.47)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Alg
import Definitions.Def_PreprocOWS_Supplement_searchWinPost
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Theorem 10.1 (One-query search bound for binary phase states, with post queries)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…),
p.43 (PDF p.46), with a minimal correction `log M → log(2M)`: for the variant of the oracle state
search game in which the adversary also makes `T` queries to `R` after the arbitrary phase query,
every such adversary with workspace dimension `M` satisfies
`E_R[Win(𝒜 | R)] ≤ O((T² + (T+1) log(2M))/K)`. The page prints `log M`.

**Formalization Note.** Correction: with `log M` the bound is `0` at `K = N = M = 1`, `T = 0`, where
`Win = 1`; `log(2M)` is the paper's own form in Theorem 1.3 (p.5, PDF p.8). The `O(·)` is one universal
`C > 0` chosen before `K, N, M, T` and the adversary; `log` is natural. `V`, `{Π_k}` (projective)
and the post-query access `Q` (query map and unitaries, run `A_R = (O_R U)^T`) are independent of
`R`; `f R` depends arbitrarily on `R`. `K ≥ 1`. -/
theorem theorem_10_1 : ∃ C : ℝ, 0 < C ∧ ∀ (K N M T : ℕ), 1 ≤ K →
    ∀ V : Matrix (Fin M) (Fin N) ℂ, IsIsometry V →
    ∀ P : Fin K → Matrix (Fin M) (Fin M) ℂ, IsProjMeas P →
    ∀ Q : QAccess K N M T, ∀ f : Oracle K N → Fin M → Bool,
      avg (fun R => searchWinPost V P Q (f R) R) ≤
        C * (((T : ℝ) ^ 2 + (T + 1) * Real.log (2 * M)) / K) := by sorry

end PreprocOWS.Supplement
