-- Prove2me | Theorems.Thm_ShadowBootstrap_corollary_5_13
-- name    : ShadowBootstrap.corollary_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:55.603276+00:00
-- url     : https://prove2.me/theorems/4f1c9bd4-93a4-43c4-86ff-945cf1ff938d
-- title:
--   Corollary 5.13 — $\mathbb E[1 - |\langle\psi|\hat\psi_\emptyset\rangle|^2] \le 4\sqrt C\sum_\ell(1/\sqrt{N_\ell} + \sqrt{2^\ell/(N_\ell S_\ell)})$
-- statement:
--   Let $|\psi\rangle$ be an $n$-qubit unit vector. Suppose the level with $n - \ell$ suffix qubits uses a Clifford ensemble with invertible shadow channel satisfying Eq. (8) with one constant $C_F$ for every state, and let $C = C_F + 1$. Let $N_\ell, S_\ell \ge 1$ for $\ell = 0, \dots, n-1$, and let the reconstruction use any rule that returns a normalized eigenvector of the largest eigenvalue of each $\hat B_x$. With the levels using independent bases and disjoint copies, the recursive reconstruction of §5.3–5.5 satisfies
--   $$\mathbb E\big[1 - |\langle\psi|\hat\psi_\emptyset\rangle|^2\big] \le 4\sqrt C\sum_{\ell=0}^{n-1}\Big(\frac{1}{\sqrt{N_\ell}} + \sqrt{\frac{2^\ell}{N_\ell S_\ell}}\Big).$$
--
--   Choosing $N_\ell$ and $S_\ell$ to make the right side small gives the initialization theorem (Theorem 5.1).
--
--   Differences from the source:
--   - reading: the suffix ensembles of Lemma 5.4 → any family of finite Clifford ensembles with invertible shadow channels satisfying Eq. (8) with one constant C_F; reason: the measurement assumptions of §5.2
--   - generalization: C (the constant of Lemma 5.9) → the explicit C = C_F + 1; reason: Lemma 5.9 holds with C_F + 1; explicit constants specialize
--   - reading: choose any normalized top eigenvector → any eigenvector rule (a function of B̂_x) returning a unit maximizer of v†B̂_xv on Hermitian matrices; reason: every deterministic choice is such a rule
--   - encoding: levels ℓ = 0, …, n−1 → levels indexed by the suffix size n − ℓ, data as histograms; reason: the same reconstruction
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Corollary 5.13 and its proof, pp.21–22

import Mathlib
import Definitions.Def_ShadowBootstrap_recon
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Corollary 5.13, p.21 (expected reconstruction error): for the recursive reconstruction,
`E[1 − |⟨ψ|ψ̂_∅⟩|²] ≤ 4√C Σ_{ℓ=0}^{n−1} (1/√N_ℓ + √(2^ℓ/(N_ℓ S_ℓ)))`.

**Formalization Note** The level with `j = n − ℓ` suffix qubits uses the ensemble `E j`, any finite
Clifford ensemble with invertible shadow channel satisfying Eq. (8) with one constant `C_F` for
every state (Lemma 5.4's measurement assumptions); `C = C_F + 1` is the constant of Lemma 5.9. The
reconstruction is `recon` (§5.3–5.5, Algorithm 3) with leaves `1 ∈ ℂ` and any eigenvector rule
`choose` satisfying `IsTopEigRule`; the levels use independent bases and disjoint copies, and the
expectation is over all levels' data (`initExpect`). `N_ℓ, S_ℓ ≥ 1`. -/
theorem corollary_5_13 (CF : ℝ) (n : ℕ) {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    (E : (j : ℕ) → Primitive j (ι j))
    (hCl : ∀ j, 1 ≤ j → j ≤ n → IsCliffordPrimitive (E j))
    (hinv : ∀ j, 1 ≤ j → j ≤ n → IsUnit (measChannel (E j)))
    (hvar : ∀ j, 1 ≤ j → j ≤ n → ∀ ρ : Op j, WildeQIT.IsDensityOperator ρ →
      ∀ O : Op j, O.IsHermitian → snapVar (E j) ρ O ≤ CF * frobSq O)
    (N S : ℕ → ℕ) (hN : ∀ ℓ < n, 1 ≤ N ℓ) (hS : ∀ ℓ < n, 1 ≤ S ℓ)
    (choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ) (hchoose : IsTopEigRule choose)
    (ψ : Bits n → ℂ) (hψ : IsUnitVec ψ) :
    initExpect E choose N S ψ (fun v => 1 - ‖braket ψ v‖ ^ 2) ≤
      4 * Real.sqrt (CF + 1) * ∑ ℓ ∈ Finset.range n,
        (1 / Real.sqrt (N ℓ) + Real.sqrt (2 ^ ℓ / ((N ℓ : ℝ) * S ℓ))) := by sorry

end ShadowBootstrap
