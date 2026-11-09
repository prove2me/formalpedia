-- Prove2me | Theorems.Thm_PreprocOWS_display_7_8
-- name    : PreprocOWS.display_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:38:09.100656+00:00
-- url     : https://prove2.me/theorems/d2e3d78c-48d0-4a06-bb0a-2b3838e1b203
-- title:
--   §5.3 Feynman path formulation: $\sum_S\|v_{t,S,x}\|^2=1$ and (7) $=$ (8)
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   Let $|\psi\rangle$ be a normalized state on (advice register)$\otimes$(database register), and let $|v_{t,S,x}\rangle$ be its Feynman-path vectors. Then
--
--   1. $\sum_S\||v_{t,S,x}\rangle\|^2=1$ for every $t\le T$ and every $x\in[N]$;
--   2. the goal (7), the winning probability $\mathrm{val}_A(\psi)$, equals
--   $$
--   \frac1{KN}\sum_{k,S}\Big\|\Pi_k\sum_x|v_{T,S\oplus(k,x),x}\rangle\Big\|^2 .\qquad(8)
--   $$
--
--   Form (8) is the starting point of the case analysis of §5.3.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - encoding: ∑_{a,y} Q_{a,y} over query values (a,y) → ∑ over o ∈ Option([K]×[N]) with S ⊕ none = S; reason: the query map's value set; the paper's case has no none
--   - generalization: §5.3 works with a start state supported on databases of size ≤ ℓ ("we are summing over D such that |D| ≤ ℓ", p.20) → no support hypothesis on ψ (any unit vector); reason: the identity/bound uses only normalization, unitarity and completeness of {Π_k}; the supported states are a special case
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.3, Feynman path formulation and displays (7)–(8), pp.20–21 (PDF pp.23–24)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_gameVal
import Definitions.Def_PreprocOWS_feynV
open Matrix

namespace PreprocOWS

/-- **§5.3, Feynman path formulation and displays (7)–(8)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), pp.20–21 (PDF pp.23–24): for a
normalized start state, `∑_S ‖|v_{t,S,x}⟩‖² = 1` for every `t ≤ T` and every `x`, and the goal (7)
equals `(1/(KN)) ∑_{k,S} ‖Π_k ∑_x |v_{T, S ⊕ (k,x), x}⟩‖²` (8).

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). The vectors `|v_{t,S,x}⟩` are `feynV A ψ t S x`, defined by the
recursion of p.20; (7) is `gameVal A ψ`. -/
theorem display_7_8 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (ψ : Fin (2 ^ S) × DB K N → ℂ) (hψ : vnormSq ψ = 1) :
    (∀ t ≤ T, ∀ x : Fin N, ∑ D : DB K N, vnormSq (feynV A ψ t D x) = 1) ∧
      gameVal A ψ = ((K : ℝ) * N)⁻¹ * ∑ k, ∑ D : DB K N,
        vnormSq (A.proj k *ᵥ ∑ x, feynV A ψ T (symmDiff D {(k, x)}) x) := by sorry

end PreprocOWS
