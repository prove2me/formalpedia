-- Prove2me | Theorems.Thm_PreprocOWS_display_11
-- name    : PreprocOWS.display_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:37:56.39736+00:00
-- url     : https://prove2.me/theorems/95b89755-2682-4418-a3eb-919011a0b5e4
-- title:
--   Display (11): $\sqrt{G_t}\le\sqrt{G_{t-1}}+\sqrt{2/K}$ and $G_T\le2(\ell/(KN)+2T^2/K)$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   Let $\ell\in\mathbb N$ and let $|\psi\rangle$ be a normalized start state supported on databases of size $\le\ell$. For every step $1\le t\le T$,
--   $$
--   B_t+C_t\le\frac1K,\qquad \sqrt{G_t}\le\sqrt{G_{t-1}}+\sqrt{C_t}+\sqrt{B_t}\le\sqrt{G_{t-1}}+\sqrt{2/K},
--   $$
--   and
--   $$
--   G_0\le\frac{\ell}{KN},\qquad G_T\le\Big(\sqrt{G_0}+T\sqrt{2/K}\Big)^2\le2\Big(\frac{\ell}{KN}+\frac{2T^2}{K}\Big).\qquad(11)
--   $$
--
--   It bounds the part where the challenge entry is not in the final database: it was either preloaded or queried.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - encoding: steps 1 ≤ t ≤ T, G_{t−1}, B_t, C_t → i : Fin T with t = i + 1: Gfun i, Bfun i, Cfun i; reason: index shift
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.3, display (11) and the induction of G_t, pp.22–23 (PDF pp.25–26)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_DB
import Definitions.Def_PreprocOWS_Gfun
open Matrix

namespace PreprocOWS

/-- **§5.3, display (11) and the induction of `G_t`**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), pp.22–23 (PDF pp.25–26): for a
normalized start state supported on databases of size `≤ ℓ`, for every step `1 ≤ t ≤ T`:
`B_t + C_t ≤ 1/K` and `√G_t ≤ √G_{t−1} + √C_t + √B_t ≤ √G_{t−1} + √(2/K)`; moreover
`G_0 ≤ ℓ/(KN)` and `G_T ≤ (√G_0 + T·√(2/K))² ≤ 2·(ℓ/(KN) + 2T²/K)`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). The step `t` is `i + 1` for `i : Fin T`, so `G_{t−1}` is `Gfun A ψ i`
and `B_t`, `C_t` are `Bfun A ψ i`, `Cfun A ψ i`. -/
theorem display_11 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (ℓ : ℕ) (ψ : Fin (2 ^ S) × DB K N → ℂ) (hψ : vnormSq ψ = 1)
    (hsupp : SupportedLE ℓ ψ) :
    (∀ i : Fin T, Bfun A ψ i + Cfun A ψ i ≤ 1 / K) ∧
      (∀ i : Fin T, Real.sqrt (Gfun A ψ (i + 1)) ≤
        Real.sqrt (Gfun A ψ i) + Real.sqrt (Cfun A ψ i) + Real.sqrt (Bfun A ψ i)) ∧
      (∀ i : Fin T, Real.sqrt (Gfun A ψ (i + 1)) ≤ Real.sqrt (Gfun A ψ i) + Real.sqrt (2 / K)) ∧
      Gfun A ψ 0 ≤ (ℓ : ℝ) / (K * N) ∧
      Gfun A ψ T ≤ (Real.sqrt (Gfun A ψ 0) + T * Real.sqrt (2 / K)) ^ 2 ∧
      (Real.sqrt (Gfun A ψ 0) + T * Real.sqrt (2 / K)) ^ 2 ≤
        2 * ((ℓ : ℝ) / (K * N) + 2 * (T : ℝ) ^ 2 / K) := by sorry

end PreprocOWS
