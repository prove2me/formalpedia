-- Prove2me | Theorems.Thm_PreprocOWS_Supplement_theorem_6_1
-- name    : PreprocOWS.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:12:07.196786+00:00
-- url     : https://prove2.me/theorems/8a4f7142-542a-4742-bff4-4e79c6d34a53
-- title:
--   Theorem 6.1 — 1OWS with $S$ bits of classical advice: winning probability $O\big((T^2+1)/K + S(T+1)/(KN)\big)$
-- statement:
--   Consider the 1OWS game of Definition 5.1. A random oracle $R:[K]\times[N]\to\{\pm1\}$ is sampled uniformly. An adversary receives one copy of $|\psi_{R,k}\rangle = N^{-1/2}\sum_x R(k,x)|x\rangle$ for a uniform key $k\in[K]$, makes $T$ queries to $R$ and measures with a projective measurement $\{\Pi_k\}$ to guess $k$. Here the advice is **classical**: an $S$-bit string $z_R\in\{0,1\}^S$ chosen arbitrarily as a function of $R$, loaded as the basis state $|z_R\rangle$; the workspace starts in $|0^w\rangle$.
--
--   There is a universal constant $C>0$ such that for all integers $S,T\ge0$, $1\le K\le N$, every workspace size $w$, every such algorithm and every advice map $R\mapsto z_R$,
--   $$
--   \mathbb E_R\,\mathbb E_k\,\Pr[\text{output }k]\,\le\,C\Big(\frac{T^2+1}{K}+\frac{S(T+1)}{KN}\Big).
--   $$
--
--   Compared with Theorem 5.2 (quantum advice, $O((T^2+1+\sqrt{S(T+1)})/K)$), classical advice gives a bound stronger by a factor of $N/K$ when $K<N$: constant success needs $ST=\Omega(KN)$.
--
--   Differences from the source:
--   - encoding: O(·) → one constant C > 0 quantified before every parameter and before the adversary; reason: the reading of O(·) used by the published goal Theorem 5.2; the proof supplies explicit constants
--   - generalization: one fixed unitary U between queries and a phase query on a designated query register → distinct unitaries U_1, …, U_T and an arbitrary query map q : [M] → Option([K]×[N]) with O_R|s⟩ = R(q(s))|s⟩; reason: the page's form is the special case of a constant U and q reading the query register; the same convention as the published base Alg
--   - encoding: maximum over advice strings z_R inside E_R → ∀ maps z : Oracle K N → [2^S] inside E_R; reason: a bound for every map is a bound on E_R max_z
--   - encoding: K ≤ N → 1 ≤ K ≤ N; reason: excludes only the empty key set, where E_k and the division by K are undefined
--   - generalization: N = 2^n (§3, p.11) → N any positive integer with 1 ≤ K ≤ N; reason: the case N = 2^n is included; the same convention as the published goal Theorem 5.2
--   - encoding: a final unitary U_{T+1} before the measurement (§3.1) → no final unitary; the measurement {Π_k} is any projective measurement; reason: U_{T+1}†Π_kU_{T+1} is again a projective measurement
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 6.1, p.23 (PDF p.26); §6.1, p.24 (PDF p.27)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Alg
import Definitions.Def_PreprocOWS_win
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- **Theorem 6.1 (Non-uniform security of 1OWS in QROM, with classical advice)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…),
p.23 (PDF p.26): for integer `S, T ≥ 0` and `K ≤ N`, the non-uniform security (with `S`-bit
advice and `T` queries) of 1OWS in QROM is `O((T² + 1)/K + S(T+1)/(KN))`; that is, the maximum
winning probability is bounded by `O((T² + 1)/K + S(T+1)/(KN))`.

**Formalization Note.** The game is that of Definition 5.1 (the base `Alg`/`win`), except that the
advice is a classical string `z_R ∈ {0,1}^S`, i.e. the basis vector `|z_R⟩` of the advice register
(§6.1, p.24: "its advice is `|z_R⟩`"), chosen arbitrarily as a function of `R` ("maximum" is `∀`
advice maps). The `O(·)` is one universal constant `C > 0`, chosen before `S, T, K, N`, the
workspace size `w` and the algorithm. The measurement is projective; `1 ≤ K ≤ N`. -/
theorem theorem_6_1 : ∃ C : ℝ, 0 < C ∧ ∀ (S T K N w : ℕ), 1 ≤ K → K ≤ N →
    ∀ A : Alg S T K N w, IsProjMeas A.proj →
    ∀ z : Oracle K N → Fin (2 ^ S),
      avg (fun R => win A R (Pi.single (z R) (1 : ℂ))) ≤
        C * (((T : ℝ) ^ 2 + 1) / K + (S : ℝ) * (T + 1) / (K * N)) := by sorry

end PreprocOWS.Supplement
