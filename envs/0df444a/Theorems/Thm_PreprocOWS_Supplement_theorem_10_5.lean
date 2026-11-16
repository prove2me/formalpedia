-- Prove2me | Theorems.Thm_PreprocOWS_Supplement_theorem_10_5
-- name    : PreprocOWS.Supplement.theorem_10_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:16:37.570223+00:00
-- url     : https://prove2.me/theorems/f40e6046-e1f0-4033-b2b3-65d9aef7bbff
-- title:
--   Theorem 10.5 — one arbitrary phase query with $t\ge1$ pre-queries and $T$ post-queries: search and distinguishing bounds
-- statement:
--   Let $R=(R(k,x))_{k\in[K],x\in[N]}$ be independent Rademacher signs. The adversary makes $t\ge1$ queries to $R$, then one arbitrary phase query $O_{f_R}$, then $T$ queries to $R$: on input $|\psi_{R,k}\rangle$ it prepares $A_RO_{f_R}V_R|\psi_{R,k}\rangle$ with $V_R=(O_RU'_t)\cdots(O_RU'_1)V_0$ and $A_R=(O_RU)^T$. Here $V_0$ is a fixed isometry, all unitaries and the query map are fixed, and $f_R$ depends arbitrarily on $R$ but not on the challenge.
--
--   There is a universal constant $C>0$ such that for all $K\ge1$, $N$, $M$, $T$, all $t\ge1$ and every such adversary:
--
--   1. (Search) for every projective measurement $\{\Pi_k\}$,
--   $$
--   \mathbb E_R[\mathrm{Win}(\mathcal A\mid R)]\,\le\,C\min\Big\{1,\ \frac{t^2}{K}+\sqrt{\frac{tT^2+t(T+1)\log M}{K}}\Big\};
--   $$
--   2. (Distinguishing) for every projection $\Pi$,
--   $$
--   \mathbb E_R[\Delta_{\mathcal A}(R)]\,\le\,C\min\Big\{1,\ \frac{t}{\sqrt K}+\Big(\frac{tT^2+t(T+1)\log M}{K}\Big)^{1/4}\Big\}.
--   $$
--
--   The case $t=0$ is Theorems 10.1 and 10.4. The bounds remain negligible when $K$ is exponential and the numbers of queries and workspace qubits are polynomial.
--
--   Differences from the source:
--   - generalization: one fixed unitary U between queries and a phase query on a designated query register → distinct unitaries U_1, …, U_T and an arbitrary query map q : [M] → Option([K]×[N]) with O_R|s⟩ = R(q(s))|s⟩; reason: the page's form is the special case of a constant U and q reading the query register; the same convention as the published base Alg
--   - encoding: V_R : the isometry that includes the t pre-queries (with fixed ancillas absorbed) → V_R = U'_{t+1}(O_R U'_t)⋯(O_R U'_1) V_0 with V_0 a fixed isometry and U'_1, …, U'_{t+1} fixed unitaries (U'_{t+1} between the last pre-query and the arbitrary phase query), using the same query map as the post-queries; reason: the page's description of V_R, written out as an algorithm U_1, O_R, …, U_t, O_R, U_{t+1} of §3.1; the page's single oracle O_R is one query map
--   - encoding: b = 1 challenge |x⟩ for uniform x (game text) → random binary phase state ψ_h, as in the Δ_𝒜 of Definition 9.4; reason: the computation does not depend on the challenge, and E_h|ψ_h⟩⟨ψ_h| = I/N = E_x|x⟩⟨x|, so both averages agree
--   - encoding: two O(·) bounds → one constant C > 0 serving both, quantified before every parameter and the adversary; reason: take the larger of the two constants
--   - encoding: E_R max_f over the arbitrary phase function f → ∀ maps f : Oracle K N → ([M] → Bool) inside E_R; reason: a bound for every map R ↦ f_R is a bound on E_R max_f (finitely many f, so the maximum is attained)
--   - encoding: K keys, bound divided by K → hypothesis 1 ≤ K; reason: excludes only the empty key set, where E_k and the division by K are undefined
--   - encoding: log M inside O(·) → natural logarithm Real.log M; reason: a change of base only rescales the constant of the O(·)
--   - generalization: N = 2^n and workspace dimension M = 2^m (§3, p.11) → any natural numbers N and M; reason: the powers of two are included; the bound is stated for the exact dimensions, and the proof does not use that they are powers of two
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 10.5, p.49 (PDF p.52); §10.3, p.49

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Alg
import Definitions.Def_PreprocOWS_Supplement_searchWinPost
import Definitions.Def_PreprocOWS_Supplement_distAdvPost
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Theorem 10.5 (One-query lower bound with pre-queries and post-queries)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.49 (PDF p.52):
for the variants of the oracle state search game and distinguishing game for the binary phase state
family, where the adversary makes `t` (`t ≥ 1`) queries to `R` before and `T` queries after the
arbitrary phase query,
`E_R[Win(𝒜 | R)] ≤ O(min{1, t²/K + √((tT² + t(T+1) log M)/K)})` (Search) and
`E_R[Δ_𝒜(R)] ≤ O(min{1, t/√K + ((tT² + t(T+1) log M)/K)^{1/4}})` (Distinguishing).

**Formalization Note.** One universal `C > 0`, chosen before `K, N, M, t, T` and the adversary,
serves both bounds; `log` is natural. The computation is `A_R O_{f_R} V_R |ψ_{R,k}⟩` with
`V_R = U'_{t+1} (O_R U'_t)⋯(O_R U'_1) V_0` (`QAccess.preIso`), `V_0` a fixed isometry `ℂ^N → ℂ^M`,
`U'_i` fixed unitaries (`U'_{t+1}` between the last pre-query and `O_{f_R}`), and the same oracle `O_R` (query map of `Q`) for pre- and post-queries. The measurement
(`{Π_k}` projective, resp. a projection `Π`) is independent of `R`; `f R` depends arbitrarily on `R`.
In the distinguishing game the `b = 1` challenge is the random binary phase state `ψ_h`, as in the
`Δ_𝒜` of Definition 9.4 (its average equals that of `|x⟩` for uniform `x`). `K ≥ 1`. -/
theorem theorem_10_5 : ∃ C : ℝ, 0 < C ∧ ∀ (K N M t T : ℕ), 1 ≤ K → 1 ≤ t →
    ∀ V₀ : Matrix (Fin M) (Fin N) ℂ, IsIsometry V₀ →
    ∀ Upre : Fin t → Matrix.unitaryGroup (Fin M) ℂ, ∀ Ufin : Matrix.unitaryGroup (Fin M) ℂ,
    ∀ Q : QAccess K N M T,
      (∀ P : Fin K → Matrix (Fin M) (Fin M) ℂ, IsProjMeas P →
        ∀ f : Oracle K N → Fin M → Bool,
          avg (fun R => searchWinPost (Q.preIso Upre Ufin V₀ R) P Q (f R) R) ≤
            C * min 1 ((t : ℝ) ^ 2 / K +
              Real.sqrt (((t : ℝ) * T ^ 2 + t * (T + 1) * Real.log M) / K))) ∧
      (∀ P : Matrix (Fin M) (Fin M) ℂ, P.IsHermitian → P * P = P →
        ∀ f : Oracle K N → Fin M → Bool,
          avg (fun R => distAdvPost (Q.preIso Upre Ufin V₀ R) P Q (f R) R) ≤
            C * min 1 ((t : ℝ) / Real.sqrt K +
              (((t : ℝ) * T ^ 2 + t * (T + 1) * Real.log M) / K) ^ ((1 : ℝ) / 4))) := by sorry

end PreprocOWS.Supplement
