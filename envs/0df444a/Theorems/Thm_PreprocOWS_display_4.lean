-- Prove2me | Theorems.Thm_PreprocOWS_display_4
-- name    : PreprocOWS.display_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:30:23.989481+00:00
-- url     : https://prove2.me/theorems/07087761-3647-4044-bc8d-5cdf8c7162da
-- title:
--   Display (4): the best winning probability is $\|Y_R\|$
-- statement:
--   Fix integers $S,T,w\ge0$ and $1\le K\le N$, and a $T$-query algorithm $A$ (query map, unitaries $U_1,\dots,U_T$, projective measurement $\{\Pi_k\}_{k\in[K]}$) with $S$ advice qubits and a $w$-qubit workspace.
--   For every oracle $R$:
--
--   1. $Y_R$ is positive semidefinite;
--   2. for every advice vector $\varphi$, $\mathrm{win}_A(R,\varphi)=\langle\varphi|Y_R|\varphi\rangle$;
--   3. the maximum of $\mathrm{win}_A(R,\varphi)$ over unit vectors $\varphi$ is attained and equals $\|Y_R\|$.
--
--   Averaging over $R$,
--   $$
--   \mathbb E_R\max_{\varphi_R}\mathbb E_k\langle\varphi_R|\langle\psi_{R,k}|\langle0^w|(U^\dagger O_R^\dagger)^T\Pi_k(O_RU)^T|\psi_{R,k}\rangle|\varphi_R\rangle|0^w\rangle=\mathbb E_R\|Y_R\| .
--   $$
--
--   This turns the security of the game against the best $R$-dependent advice into the average operator norm of a random matrix.
--
--   Differences from the source:
--   - generalization: one intermediate unitary U between queries (§3.1: "without loss of generality … the same U") → distinct unitaries U_1, …, U_T; reason: the paper's algorithm is the case U_i = U; the proof never uses equality of the U_i
--   - generalization: phase query O_R on a designated query register |a,y⟩ → a query map q : Ω → Option([K]×[N]), O_R|s⟩ = R(q(s))|s⟩ with R(none) = 1; reason: the paper's oracle is the case where q reads the query register (none on unused basis states)
--   - generalization: N = 2^n (§3) → N any positive integer with K ≤ N; reason: the case N = 2^n is included; the proof does not use it
--   - encoding: [K] = {1,…,K}, [N], R : [K]×[N] → {±1} → Fin K, Fin N, R : Fin K × Fin N → Bool with sign sgn; reason: 0-based relabelling; the same 2^{KN} functions
--   - encoding: final projective measurement {Π_k} → Π_k Hermitian, Π_k² = Π_k, ∑_k Π_k = 1 (hypothesis IsProjMeas); reason: the definition of a projective measurement
--   - generalization: E_R max_{φ_R}(…) = E_R‖Y_R‖ (an identity of averages) → for every R: Y_R ⪰ 0, win = ⟨φ|Y_R|φ⟩, and ‖Y_R‖ is the attained maximum over unit φ; reason: the per-R statement implies the averaged identity
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, display (4), p.17 (PDF p.20)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_win
import Definitions.Def_PreprocOWS_Ymat
open Matrix
open scoped ComplexOrder

namespace PreprocOWS

/-- **§5.1, display (4)**, Dong–Lombardi, *Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), p.17 (PDF p.20): for every oracle `R`, the winning probability with
advice `|φ⟩` is the quadratic form `⟨φ|Y_R|φ⟩` of the positive semidefinite matrix `Y_R`, and its
maximum over unit advice is the operator norm `‖Y_R‖`; hence
`E_R max_{φ_R} E_k ⟨φ_R|⟨ψ_{R,k}|⟨0^w| (U†O_R†)^T Π_k (O_R U)^T |ψ_{R,k}⟩|φ_R⟩|0^w⟩ = E_R‖Y_R‖`.

**Formalization Note.** `A` is a `T`-query algorithm (query map, unitaries `U_1, …, U_T`, measurement `{Π_k}`), `{Π_k}`
is a projective measurement, and `1 ≤ K ≤ N` (Definition 5.1, p.16). The statement is per `R`, which gives the averaged identity of the
page. -/
theorem display_4 {S T K N w : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (A : Alg S T K N w)
    (hA : IsProjMeas A.proj) (R : Oracle K N) :
    (Ymat A R).PosSemidef ∧
      (∀ φ : Fin (2 ^ S) → ℂ, ((win A R φ : ℝ) : ℂ) = star φ ⬝ᵥ (Ymat A R *ᵥ φ)) ∧
      IsGreatest {r : ℝ | ∃ φ : Fin (2 ^ S) → ℂ, vnormSq φ = 1 ∧ win A R φ = r} (opNorm (Ymat A R)) := by sorry

end PreprocOWS
