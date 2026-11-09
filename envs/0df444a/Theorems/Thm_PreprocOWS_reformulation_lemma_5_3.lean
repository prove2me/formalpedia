-- Prove2me | Theorems.Thm_PreprocOWS_reformulation_lemma_5_3
-- name    : PreprocOWS.reformulation_lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:34:46.701574+00:00
-- url     : https://prove2.me/theorems/a86b757a-3bd9-40f4-a615-85ff65049d14
-- title:
--   Reformulation of Lemma 5.3: $\langle\psi|\widehat Y|\psi\rangle$ is a winning probability
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   For every state $|\psi\rangle$ on (advice register)$\otimes$(database register),
--   $$
--   \langle\psi|\,\widehat Y\,|\psi\rangle=\mathbb E_k\Big\|\Pi_k(\mathsf{cO}\,U)^T\Big(\frac1{\sqrt N}\sum_x|x\rangle\otimes T_{k,x}\Big)|\psi\rangle|0^w\rangle\Big\|^2=\mathrm{val}_A(\psi),
--   $$
--   the winning probability of the 1OWS game started from $|\psi\rangle$ in the compressed oracle database mode. In particular $|\langle\psi|\widehat Y|\psi\rangle|$ equals it.
--
--   This reduces Lemma 5.3 to a bound on a search game with a preloaded database (Lemma 5.4).
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - reading: Ŷ = (1/N)·E_k ∑_{x1,x2} ⟨x1|⟨0^w|(U†cO†)^TΠ_k(cO U)^T|x2⟩|0^w⟩ ⊗ T_{k,x1}T_{k,x2} → Ŷ = (1/N)·E_k ∑_{x1,x2} T_{k,x1}·(block)·T_{k,x2}; reason: the block acts on the database register through cO, so the tensor is ambiguous; this is the reading under which Ŷ is Hermitian and the Reformulation of Lemma 5.3 holds
--   - reading: T_{k,(x1⊕x2)} in the first line of the display → T_{k,x1}·(block)·T_{k,x2}, as in the definition of Ŷ; reason: the same operator: D ↦ D ⊕ {(k,x1)} ⊕ {(k,x2)}
--   - generalization: |⟨ψ|Ŷ|ψ⟩| = E_k‖…‖² for normalized ψ → ⟨ψ|Ŷ|ψ⟩ = val_A(ψ) as complex numbers, for every ψ; reason: taking absolute values of a unit ψ gives the page's statement
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Reformulation of Lemma 5.3, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_PreprocOWS_Yhat
import Definitions.Def_PreprocOWS_gameVal
open Matrix

namespace PreprocOWS

/-- **Reformulation of Lemma 5.3**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.19 (PDF p.22): for a state `|ψ⟩` on (advice register) ⊗
(database register),
`|⟨ψ|Ŷ|ψ⟩| = E_k ‖Π_k (cO U)^T ((1/√N) ∑_x |x⟩ ⊗ T_{k,x}) |ψ⟩|0^w⟩‖²`, the winning probability
`gameVal A ψ` of the 1OWS game started from `|ψ⟩`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). Stated as the equality `⟨ψ|Ŷ|ψ⟩ = gameVal A ψ` of complex numbers
for every `ψ` (normalized or not), which implies the page's equality of absolute values. -/
theorem reformulation_lemma_5_3 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (ψ : Fin (2 ^ S) × DB K N → ℂ) :
    star ψ ⬝ᵥ (Yhat A *ᵥ ψ) = ((gameVal A ψ : ℝ) : ℂ) := by sorry

end PreprocOWS
