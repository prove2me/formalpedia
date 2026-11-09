-- Prove2me | Theorems.Thm_PreprocOWS_display_9
-- name    : PreprocOWS.display_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:40:08.755187+00:00
-- url     : https://prove2.me/theorems/4dac161a-e26b-458f-88c7-ab13f2468d52
-- title:
--   Display (9): $H_T\le H_0\le\ell/(K\lfloor\sqrt\ell\rfloor)\le2\sqrt\ell/K$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   Let $\ell\ge1$ and let $|\psi\rangle=\sum_D\alpha_D|\varphi_D\rangle|D\rangle$ be a normalized state supported on databases of size $\le\ell$. Then $H_t\le H_{t-1}$ for $1\le t\le T$, and
--   $$
--   H_T\le H_0=\frac1{KN}\sum_{\substack{k,S,x\\|S_k|>\sqrt\ell}}|\alpha_{S\oplus(k,x)}|^2\le\frac{\ell}{K\lfloor\sqrt\ell\rfloor}\le\frac{2\sqrt\ell}{K},
--   $$
--   where $|\alpha_D|^2=\sum_z|\psi(z,D)|^2$.
--
--   It disposes of final databases with a large row at the challenge key.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - encoding: H_t ≤ H_{t−1} for 1 ≤ t ≤ T → H_{t+1} ≤ H_t for t < T; reason: index shift
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.3, display (9), p.21 (PDF p.24)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_DB
import Definitions.Def_PreprocOWS_Hfun
open Matrix

namespace PreprocOWS

/-- **§5.3, display (9)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.21 (PDF p.24): for `ℓ ≥ 1` and a normalized start state
supported on databases of size `≤ ℓ`, `H_t ≤ H_{t−1}` for `1 ≤ t ≤ T`, and
`H_T ≤ H_0 = (1/(KN)) ∑_{k,S,x : |S_k| > √ℓ} |α_{S ⊕ (k,x)}|² ≤ ℓ/(K⌊√ℓ⌋) ≤ 2√ℓ/K`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). `|α_D|² = ∑_z |ψ(z,D)|²`; `⌊√ℓ⌋` is `Nat.sqrt ℓ`. The step is stated
as `H_{t+1} ≤ H_t` for `t < T`. -/
theorem display_9 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ψ : Fin (2 ^ S) × DB K N → ℂ) (hψ : vnormSq ψ = 1)
    (hsupp : SupportedLE ℓ ψ) :
    (∀ t < T, Hfun A ℓ ψ (t + 1) ≤ Hfun A ℓ ψ t) ∧
      Hfun A ℓ ψ 0 = ((K : ℝ) * N)⁻¹ *
        ∑ k, ∑ D ∈ Finset.univ.filter (fun D : DB K N => Real.sqrt ℓ < rowCard D k),
          ∑ x : Fin N, ∑ z : Fin (2 ^ S), ‖ψ (z, symmDiff D {(k, x)})‖ ^ 2 ∧
      Hfun A ℓ ψ 0 ≤ (ℓ : ℝ) / (K * Nat.sqrt ℓ) ∧
      (ℓ : ℝ) / (K * Nat.sqrt ℓ) ≤ 2 * Real.sqrt ℓ / K := by sorry

end PreprocOWS
