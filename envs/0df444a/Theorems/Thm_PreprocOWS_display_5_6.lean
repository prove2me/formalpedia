-- Prove2me | Theorems.Thm_PreprocOWS_display_5_6
-- name    : PreprocOWS.display_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:32:27.613203+00:00
-- url     : https://prove2.me/theorems/68dd3f3c-33c0-4f6d-8dbf-c44f38d8e131
-- title:
--   Displays (5)–(6): $\mathbb E_R\mathrm{Tr}(Y_R^{2t})=\sum_z\langle z|\langle\emptyset|\widehat Y^{2t}|z\rangle|\emptyset\rangle$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   For every $t\ge0$,
--   $$
--   \mathbb E_R\,\mathrm{Tr}\big(Y_R^{2t}\big)=\sum_{z\in[2^S]}\mathbb E_R\langle z|Y_R^{2t}|z\rangle \qquad(5)
--   $$
--   and
--   $$
--   \mathbb E_R\,\mathrm{Tr}\big(Y_R^{2t}\big)=\sum_{z\in[2^S]}\langle z|\langle\emptyset|\,\widehat Y^{2t}\,|z\rangle|\emptyset\rangle .\qquad(6)
--   $$
--
--   Display (6) moves the trace moment into the compressed oracle database mode, starting from the empty database.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - reading: Ŷ = (1/N)·E_k ∑_{x1,x2} ⟨x1|⟨0^w|(U†cO†)^TΠ_k(cO U)^T|x2⟩|0^w⟩ ⊗ T_{k,x1}T_{k,x2} → Ŷ = (1/N)·E_k ∑_{x1,x2} T_{k,x1}·(block)·T_{k,x2}; reason: the block acts on the database register through cO, so the tensor is ambiguous; this is the reading under which Ŷ is Hermitian and the Reformulation of Lemma 5.3 holds
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, displays (5) and (6), p.18 (PDF p.21)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Ymat
import Definitions.Def_PreprocOWS_Yhat
open Matrix

namespace PreprocOWS

/-- **§5.1, displays (5) and (6)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.18 (PDF p.21): for every `t`,
`E_R Tr(Y_R^{2t}) = ∑_{z ∈ [2^S]} E_R ⟨z|Y_R^{2t}|z⟩` (5) and
`E_R Tr(Y_R^{2t}) = ∑_{z ∈ [2^S]} ⟨z|⟨∅| Ŷ^{2t} |z⟩|∅⟩` (6).

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). `E_R` is the uniform average over all `2^{KN}` oracles; both
identities are equalities of complex numbers. -/
theorem display_5_6 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (t : ℕ) :
    avg (fun R : Oracle K N => (Ymat A R ^ (2 * t)).trace) =
        ∑ z, avg (fun R : Oracle K N => (Ymat A R ^ (2 * t)) z z) ∧
      avg (fun R : Oracle K N => (Ymat A R ^ (2 * t)).trace) =
        ∑ z, (Yhat A ^ (2 * t)) (z, ∅) (z, ∅) := by sorry

end PreprocOWS
