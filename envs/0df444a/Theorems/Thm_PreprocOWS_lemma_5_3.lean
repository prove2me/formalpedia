-- Prove2me | Theorems.Thm_PreprocOWS_lemma_5_3
-- name    : PreprocOWS.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:32:42.917766+00:00
-- url     : https://prove2.me/theorems/3b962d12-0914-4835-9398-86ca7fa856ce
-- title:
--   Lemma 5.3: $|\langle\psi|\widehat Y|\psi\rangle|\le10(T^2+\sqrt\ell)/K$ on databases of size $\le\ell$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   If a normalized state $|\psi\rangle$ on (advice register)$\otimes$(database register) is supported on databases of size $\le\ell$, then
--   $$
--   \big|\langle\psi|\,\widehat Y\,|\psi\rangle\big|\le c\cdot\frac{T^2+\max\{\sqrt\ell,1\}}{K},\qquad c=10 .
--   $$
--   For $1\le\ell\le K^2$ this is the bound $c\,(T^2+\sqrt\ell)/K$ of the lemma, and for $\ell=0$ it is the lemma's replacement of $\sqrt\ell$ by $\max\{\sqrt\ell,1\}$.
--
--   It controls one application of $\widehat Y$ on small databases, which drives the growth bound in the proof of Theorem 5.2.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - reading: Ŷ = (1/N)·E_k ∑_{x1,x2} ⟨x1|⟨0^w|(U†cO†)^TΠ_k(cO U)^T|x2⟩|0^w⟩ ⊗ T_{k,x1}T_{k,x2} → Ŷ = (1/N)·E_k ∑_{x1,x2} T_{k,x1}·(block)·T_{k,x2}; reason: the block acts on the database register through cO, so the tensor is ambiguous; this is the reading under which Ŷ is Hermitian and the Reformulation of Lemma 5.3 holds
--   - generalization: 1 ≤ ℓ ≤ K², and ℓ = 0 with max{√ℓ, 1} → every ℓ ∈ ℕ, with max{√ℓ, 1}; reason: for 1 ≤ ℓ ≤ K² max{√ℓ,1} = √ℓ and ℓ = 0 is the page's clause; for ℓ > K² the bound exceeds 10 ≥ |⟨ψ|Ŷ|ψ⟩|
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Lemma 5.3, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_DB
import Definitions.Def_PreprocOWS_Yhat
open Matrix

namespace PreprocOWS

/-- **Lemma 5.3**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.18 (PDF p.21): if a normalized state `|ψ⟩` on (advice register) ⊗
(database register) is supported on databases of size `≤ ℓ`, then
`|⟨ψ|Ŷ|ψ⟩| ≤ c · (T² + √ℓ)/K` with `c = 10`, for `1 ≤ ℓ ≤ K²`; for `ℓ = 0`, `√ℓ` is replaced by
`max{√ℓ, 1}`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). The constant is the page's `c = 10`. The bound is stated with
`max{√ℓ, 1}` for every `ℓ` (for `ℓ ≥ 1` this is `√ℓ`); for `ℓ > K²` it holds because
`10 · √ℓ / K > 10` exceeds `|⟨ψ|Ŷ|ψ⟩| ≤ 1`. -/
theorem lemma_5_3 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (ℓ : ℕ) (ψ : Fin (2 ^ S) × DB K N → ℂ) (hψ : vnormSq ψ = 1)
    (hsupp : SupportedLE ℓ ψ) :
    ‖star ψ ⬝ᵥ (Yhat A *ᵥ ψ)‖ ≤ 10 * ((T : ℝ) ^ 2 + max (Real.sqrt ℓ) 1) / K := by sorry

end PreprocOWS
