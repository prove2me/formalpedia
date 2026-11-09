-- Prove2me | Theorems.Thm_PreprocOWS_display_10
-- name    : PreprocOWS.display_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:36:44.511214+00:00
-- url     : https://prove2.me/theorems/d06b143c-adba-4ff2-bbf1-51602c3575a5
-- title:
--   Display (10): the "final database with $x$" part is $\le(\sqrt\ell+T)/K$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   Let $\ell\in\mathbb N$ and let $|\psi\rangle$ be a normalized start state. Then
--   $$
--   \frac1{KN}\sum_{\substack{k,S\\|S_k|\le\sqrt\ell+T}}\Big\|\Pi_k\sum_{x\in S_k}|v_{T,S\oplus(k,x),x}\rangle\Big\|^2\le\frac{\sqrt\ell+T}{K} .
--   $$
--
--   The sum over the few $x$ in a small row is paid for by Cauchy–Schwarz and the completeness of the measurement.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - generalization: §5.3 works with a start state supported on databases of size ≤ ℓ ("we are summing over D such that |D| ≤ ℓ", p.20) → no support hypothesis on ψ (any unit vector); ℓ is only a parameter of the row filter; reason: the identity/bound uses only normalization, unitarity and completeness of {Π_k}; the supported states are a special case
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.3, display (10), p.21 (PDF p.24)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_DB
import Definitions.Def_PreprocOWS_feynV
open Matrix

namespace PreprocOWS

/-- **§5.3, display (10)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.21 (PDF p.24): for a normalized start state,
`(1/(KN)) ∑_{k,S : |S_k| ≤ √ℓ+T} ‖Π_k ∑_{x ∈ S_k} |v_{T,S⊕(k,x),x}⟩‖² ≤ (√ℓ + T)/K`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). `x ∈ S_k` means `(k,x) ∈ S`. The middle equalities of (10) are proof
steps and are not posed. -/
theorem display_10 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (ℓ : ℕ) (ψ : Fin (2 ^ S) × DB K N → ℂ) (hψ : vnormSq ψ = 1) :
    ((K : ℝ) * N)⁻¹ *
        ∑ k, ∑ D ∈ Finset.univ.filter (fun D : DB K N => (rowCard D k : ℝ) ≤ Real.sqrt ℓ + T),
          vnormSq (A.proj k *ᵥ ∑ x ∈ Finset.univ.filter (fun x => (k, x) ∈ D),
            feynV A ψ T (symmDiff D {(k, x)}) x) ≤
      (Real.sqrt ℓ + T) / K := by sorry

end PreprocOWS
