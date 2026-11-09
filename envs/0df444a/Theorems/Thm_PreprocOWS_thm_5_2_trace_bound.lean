-- Prove2me | Theorems.Thm_PreprocOWS_thm_5_2_trace_bound
-- name    : PreprocOWS.thm_5_2_trace_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:33:06.738038+00:00
-- url     : https://prove2.me/theorems/1fa96f66-ff44-4922-a832-b5df88134757
-- title:
--   Proof of Theorem 5.2: $\mathbb E_R\|Y_R\|\le2^{S/2t}\cdot10\cdot\frac{T^2+\sqrt{t(2T+2)}}K$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   For every integer $t\ge1$:
--
--   1. for every $z\in[2^S]$, $\langle z|\langle\emptyset|\,\widehat Y^{2t}|z\rangle|\emptyset\rangle=\||\psi_z^t\rangle\|^2$;
--   2. $\displaystyle\sum_{z\in[2^S]}\langle z|\langle\emptyset|\,\widehat Y^{2t}|z\rangle|\emptyset\rangle\le2^S\cdot\Big(c\cdot\frac{T^2+\sqrt{t(2T+2)}}{K}\Big)^{2t}$;
--   3. $\displaystyle\mathbb E_R\|Y_R\|\le2^{S/2t}\cdot c\cdot\frac{T^2+\sqrt{t(2T+2)}}{K}$,
--
--   with $c=10$.
--
--   Choosing $t$ of order $S$ makes the factor $2^{S/2t}$ a constant, which gives Theorem 5.2.
--
--   **Formalization Note** The diagonal entries are complex numbers; item 2 sums their real parts.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - reading: Ŷ = (1/N)·E_k ∑_{x1,x2} ⟨x1|⟨0^w|(U†cO†)^TΠ_k(cO U)^T|x2⟩|0^w⟩ ⊗ T_{k,x1}T_{k,x2} → Ŷ = (1/N)·E_k ∑_{x1,x2} T_{k,x1}·(block)·T_{k,x2}; reason: the block acts on the database register through cO, so the tensor is ambiguous; this is the reading under which Ŷ is Hermitian and the Reformulation of Lemma 5.3 holds
--   - reading: ⟨z|⟨∅|Y^{2t}|z⟩|∅⟩ (printed Y) → the entries of Ŷ^{2t}; reason: the lines continue the bound on (6), which is about Ŷ; Y^{2t} is a missing hat
--   - encoding: ∑_z ⟨z|⟨∅|Ŷ^{2t}|z⟩|∅⟩ (a real number) → the real part of each diagonal entry, .re; reason: the first clause shows each entry equals a squared norm, so it is real; re changes no value
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), proof of Theorem 5.2, trace and norm bounds, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_Ymat
import Definitions.Def_PreprocOWS_Yhat
open Matrix

namespace PreprocOWS

/-- **Proof of Theorem 5.2, trace and norm bounds**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.19 (PDF p.22): for every integer
`t ≥ 1` and every `z`, `⟨z|⟨∅|Ŷ^{2t}|z⟩|∅⟩ = ‖|ψ_z^t⟩‖²`, and
`∑_{z ∈ [2^S]} ⟨z|⟨∅|Ŷ^{2t}|z⟩|∅⟩ ≤ 2^S · (c · (T² + √(t(2T+2)))/K)^{2t}`, and
`E_R‖Y_R‖ ≤ 2^{S/2t} · c · (T² + √(t(2T+2)))/K`, with `c = 10`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). The page writes `Y^{2t}` for `Ŷ^{2t}` in these lines. `2^{S/2t}`
is a real power. The page's choice `t = max{S/2, 1}` is not posed. -/
theorem thm_5_2_trace_bound {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (t : ℕ) (ht : 1 ≤ t) :
    (∀ z : Fin (2 ^ S), (Yhat A ^ (2 * t)) (z, ∅) (z, ∅) =
        ((vnormSq (Yhat A ^ t *ᵥ (Pi.single (z, ∅) 1 : Fin (2 ^ S) × DB K N → ℂ)) : ℝ) : ℂ)) ∧
      ∑ z : Fin (2 ^ S), ((Yhat A ^ (2 * t)) (z, ∅) (z, ∅)).re ≤
        2 ^ S * (10 * ((T : ℝ) ^ 2 + Real.sqrt ((t * (2 * T + 2) : ℕ) : ℝ)) / K) ^ (2 * t) ∧
      avg (fun R : Oracle K N => opNorm (Ymat A R)) ≤
        (2 : ℝ) ^ ((S : ℝ) / (2 * t)) * (10 * ((T : ℝ) ^ 2 + Real.sqrt ((t * (2 * T + 2) : ℕ) : ℝ)) / K) := by sorry

end PreprocOWS
