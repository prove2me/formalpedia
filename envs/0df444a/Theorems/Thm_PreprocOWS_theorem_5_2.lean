-- Prove2me | Theorems.Thm_PreprocOWS_theorem_5_2
-- name    : PreprocOWS.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:40:47.317287+00:00
-- url     : https://prove2.me/theorems/bb730d2d-e09e-4957-8ff6-9550928977f1
-- title:
--   Theorem 5.2: non-uniform security of 1OWS in QROM is $O\big((T^2+1+\sqrt{S(T+1)})/K\big)$
-- statement:
--   In the 1OWS security game a function $R:[K]\times[N]\to\{\pm1\}$ is sampled uniformly and an algorithm receives an $S$-qubit advice state $|\varphi_R\rangle$ that depends arbitrarily on $R$. A uniform key $k\in[K]$ is drawn and the algorithm receives one copy of the binary phase state $|\psi_{R,k}\rangle=N^{-1/2}\sum_xR(k,x)|x\rangle$, makes $T$ quantum queries to $R$ (with a workspace of any number $w$ of qubits started at $|0^w\rangle$) and measures a guess $k'$; it wins if $k'=k$.
--
--   There is an absolute constant $C>0$ such that for all integers $S,T\ge0$ and $1\le K\le N$, every such algorithm and every choice of advice,
--   $$
--   \mathbb E_R\,\mathbb E_k\,\Pr[\text{the algorithm outputs }k]\le C\cdot\frac{T^2+1+\sqrt{S(T+1)}}{K}.
--   $$
--
--   For $K=N$ an attacker needs advice of order $N^2$ qubits (for $T$ small) to recover the key with constant probability, against order $N$ bits for classical one-way functions.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - reading: O((T²+1+√(S(T+1)))/K) → ∃ C > 0, chosen before S, T, K, N, w and the algorithm, bounding by C·(T²+1+√(S(T+1)))/K; reason: the paper's usage: the constant of the proof is absolute (c = 10)
--   - encoding: the maximum winning probability over S-qubit advice depending arbitrarily on R → for every map φ from oracles to unit vectors of ℂ^{2^S}, E_R win(R, φ R) ≤ bound; reason: a bound for every advice map is a bound on the maximum; pure advice as in the §5.1 display (mixed advice is a convex combination)
--   - encoding: a final unitary U_{t+1} before the output (§3.1) → no final unitary; the measurement {Π_k} is arbitrary projective; reason: U_{T+1}†Π_kU_{T+1} is again a projective measurement
--   - encoding: [K] for a positive integer K; K ≤ N → 1 ≤ K and K ≤ N; reason: the paper's standing assumptions
--   - encoding: workspace of w qubits starting at |0^w⟩ (§5.1) → w universally quantified; registers ordered advice ⊗ challenge ⊗ workspace; reason: any workspace size; register order is immaterial
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Theorem 5.2, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_win
open Matrix

namespace PreprocOWS

/-- **Theorem 5.2 (Non-uniform security of 1OWS in QROM)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.16 (PDF p.19): for integer
`S, T ≥ 0`, `K ≤ N`, the non-uniform security (with `S`-qubit advice and `T` queries) of 1OWS in QROM is
`O((T² + 1 + √(S(T+1)))/K)`; that is, the maximum winning probability is bounded by
`O((T² + 1 + √(S(T+1)))/K)`.

**Formalization Note.** The `O(·)` is one universal constant `C > 0`, chosen before `S, T, K, N`, the
workspace size `w` and the algorithm. The winning probability is averaged over a uniform oracle
`R : [K]×[N] → {±1}` and a uniform key `k`; the advice `φ R` is an arbitrary unit vector on `S` qubits
depending on `R` only ("maximum" is `∀` advice maps). The algorithm has a query map, `T` unitaries and
a projective `K`-outcome measurement; `1 ≤ K ≤ N` and `N` is any positive integer. -/
theorem theorem_5_2 : ∃ C : ℝ, 0 < C ∧ ∀ (S T K N w : ℕ), 1 ≤ K → K ≤ N →
    ∀ A : Alg S T K N w, IsProjMeas A.proj →
    ∀ φ : Oracle K N → Fin (2 ^ S) → ℂ, (∀ R, vnormSq (φ R) = 1) →
      avg (fun R => win A R (φ R)) ≤ C * ((T : ℝ) ^ 2 + 1 + Real.sqrt ((S : ℝ) * (T + 1))) / K := by sorry

end PreprocOWS
