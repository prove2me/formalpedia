-- Prove2me | Theorems.Thm_PreprocOWS_lemma_5_4
-- name    : PreprocOWS.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:36:14.014056+00:00
-- url     : https://prove2.me/theorems/ecf6eac1-f535-46a3-8934-8ce3230babcc
-- title:
--   Lemma 5.4: the 1OWS game from a database of size $\le\ell$ is won with probability $\le10(T^2+\sqrt\ell)/K$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   Let $\ell\ge1$ and let $|\psi\rangle=\sum_D\alpha_D|\varphi_D\rangle|D\rangle$ be a normalized state on (advice register)$\otimes$(database register) supported on databases of size $\le\ell$. Then the winning probability of the 1OWS game started from $|\psi\rangle$ in the compressed oracle database mode satisfies
--   $$
--   \mathrm{val}_A(\psi)\le c\cdot\frac{T^2+\sqrt\ell}{K},\qquad c=10 .
--   $$
--
--   This is the search bound behind Lemma 5.3, proved in §5.3.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - generalization: 1 ≤ ℓ ≤ K² (the range of Lemma 5.3, of which this is the reformulation) → every ℓ ≥ 1; reason: the case ℓ ≤ K² is included; for ℓ > K² the bound exceeds 10 ≥ val_A(ψ)
--   - encoding: start state ∑_D α_D|φ_D⟩|D⟩ on the algorithm's register and the database register → a unit vector ψ on [2^S] × databases; the challenge and the workspace |0^w⟩ are added by Ĉ_k; reason: the state of the Reformulation; an algorithm register larger than the advice is absorbed by enlarging S
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Lemma 5.4, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_DB
import Definitions.Def_PreprocOWS_gameVal
open Matrix

namespace PreprocOWS

/-- **Lemma 5.4 (Reformulation of Lemma 5.3)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.19 (PDF p.22): in the 1OWS security game
where the algorithm starts with a state `∑_D α_D |φ_D⟩|D⟩` supported on databases of size `≤ ℓ` in the
compressed oracle database mode, the winning probability is bounded by `c · (T² + √ℓ)/K`, `c = 10`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). The start state is any unit vector `ψ` on (advice register) ⊗
(database register) with `ψ(z, D) = 0` for `|D| > ℓ`; `ℓ ≥ 1` (Lemma 5.3's range), with no upper cap
(for `ℓ > K²` the bound exceeds `1`). -/
theorem lemma_5_4 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ψ : Fin (2 ^ S) × DB K N → ℂ) (hψ : vnormSq ψ = 1)
    (hsupp : SupportedLE ℓ ψ) :
    gameVal A ψ ≤ 10 * ((T : ℝ) ^ 2 + Real.sqrt ℓ) / K := by sorry

end PreprocOWS
