-- Prove2me | Theorems.Thm_PreprocOWS_thm_5_2_step_bound
-- name    : PreprocOWS.thm_5_2_step_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:34:11.660037+00:00
-- url     : https://prove2.me/theorems/53bd5f0a-0a6d-4ef3-adaf-ba924ca7d3ee
-- title:
--   Proof of Theorem 5.2: each $\widehat Y$ adds $\le2T+2$ entries, and $\|\psi_z^i\|\le10\frac{T^2+\sqrt{(2T+2)i}}K\|\psi_z^{i-1}\|$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   Then:
--
--   1. $\widehat Y$ maps states supported on databases of size $\le m$ to states supported on databases of size $\le m+2T+2$;
--   2. for every $z\in[2^S]$ and $i\ge1$, the vector $|\psi^i_z\rangle:=\widehat Y^{\,i}|z\rangle|\emptyset\rangle$ is supported on databases of size $\le(2T+2)i$, and
--   $$
--   \big\||\psi_z^i\rangle\big\|\le c\cdot\frac{T^2+\sqrt{(2T+2)i}}{K}\cdot\big\||\psi_z^{i-1}\rangle\big\|,\qquad c=10 .
--   $$
--
--   Iterating this bound controls the diagonal entries of $\widehat Y^{2t}$ at the empty database.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - reading: Ŷ = (1/N)·E_k ∑_{x1,x2} ⟨x1|⟨0^w|(U†cO†)^TΠ_k(cO U)^T|x2⟩|0^w⟩ ⊗ T_{k,x1}T_{k,x2} → Ŷ = (1/N)·E_k ∑_{x1,x2} T_{k,x1}·(block)·T_{k,x2}; reason: the block acts on the database register through cO, so the tensor is ambiguous; this is the reading under which Ŷ is Hermitian and the Reformulation of Lemma 5.3 holds
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), proof of Theorem 5.2, step bound, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_DB
import Definitions.Def_PreprocOWS_Yhat
open Matrix

namespace PreprocOWS

/-- **Proof of Theorem 5.2, step bound**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.19 (PDF p.22): each application of `Ŷ` enlarges
the database by at most `2T + 2`; hence `|ψ_z^i⟩ := Ŷ^i |z⟩|∅⟩` is supported on databases of size
`≤ (2T+2)i`, and `‖|ψ_z^i⟩‖ ≤ c · (T² + √((2T+2)i))/K · ‖|ψ_z^{i−1}⟩‖` with `c = 10`, for every
`i ≥ 1`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). `|z⟩|∅⟩` is the basis vector `Pi.single (z, ∅) 1`; `‖·‖` is
`vnorm`. No cap on `i` (the page has none). -/
theorem thm_5_2_step_bound {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) :
    (∀ (m : ℕ) (ψ : Fin (2 ^ S) × DB K N → ℂ), SupportedLE m ψ →
        SupportedLE (m + (2 * T + 2)) (Yhat A *ᵥ ψ)) ∧
      ∀ (z : Fin (2 ^ S)) (i : ℕ), 1 ≤ i →
        SupportedLE ((2 * T + 2) * i)
            (Yhat A ^ i *ᵥ (Pi.single (z, ∅) 1 : Fin (2 ^ S) × DB K N → ℂ)) ∧
          vnorm (Yhat A ^ i *ᵥ (Pi.single (z, ∅) 1 : Fin (2 ^ S) × DB K N → ℂ)) ≤
            10 * ((T : ℝ) ^ 2 + Real.sqrt (((2 * T + 2) * i : ℕ) : ℝ)) / K *
              vnorm (Yhat A ^ (i - 1) *ᵥ (Pi.single (z, ∅) 1 : Fin (2 ^ S) × DB K N → ℂ)) := by sorry

end PreprocOWS
