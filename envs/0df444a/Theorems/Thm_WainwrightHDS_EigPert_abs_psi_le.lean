-- Prove2me | Theorems.Thm_WainwrightHDS_EigPert_abs_psi_le
-- name    : WainwrightHDS.EigPert.abs_psi_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-30T00:28:22.312244+00:00
-- url     : https://prove2.me/theorems/63f3da69-5a31-433f-8370-2bc54d77ab05
-- title:
--   Proof of Theorem 8.5, p. 244 — $|\Psi(\widehat\Delta; P)| \le 2(1-\varrho^2)|||\widetilde P|||_2 + 2\varrho\sqrt{1-\varrho^2}\,\|\tilde p\|_2$
-- statement:
--   Let $U$ be an orthogonal $d \times d$ matrix ($d \ge 1$) whose first column is $\theta^*$, let $P$ be a real symmetric $d \times d$ matrix, and write $\widetilde P = U^\top P U$ with off-diagonal block $\tilde p \in \mathbb{R}^{d-1}$ as in (8.11). Let $\widehat\theta$ be a unit vector with
--
--   $$
--   \varrho := \langle \widehat\theta, \theta^* \rangle \ge 0,
--   $$
--
--   and let $\widehat\Delta = \widehat\theta - \theta^*$. Then
--
--   $$
--   \bigl|\Psi(\widehat\Delta; P)\bigr| \;\le\; 2(1 - \varrho^2)\, |||\widetilde P|||_2 \;+\; 2\varrho\sqrt{1 - \varrho^2}\, \|\tilde p\|_2 .
--   $$
--
--   This is the bound on the right-hand side of the basic inequality (8.15) that, combined with Lemma 8.6 and $|||\widetilde P|||_2 = |||P|||_2$, yields the perturbation bound (8.12).
--
--   **Formalization Note** The first column of $U$ is column `0`; $\theta^*$ is automatically a unit vector (a column of an orthogonal matrix), and $\varrho \le 1$ follows from the Cauchy–Schwarz inequality, so neither is a hypothesis. The operator norm is that of $\widetilde P = U^\top P U$, as printed.
--
--   Differences from the source:
--   - generalization: U the orthonormal matrix of eigenvectors of Σ with first column θ*, θ* the maximal eigenvector of Σ, θ̂ the maximal eigenvector of Σ̂ → U any orthogonal matrix with first column θ*, θ̂ any unit vector, no Σ; reason: the display's derivation (θ̂ = ϱθ* + √(1−ϱ²) z with z ⊥ θ*, Uᵀθ* = e₁, ‖z̃‖ ≤ 1, |p̃₁₁| ≤ |||P̃|||₂) uses only these facts; taking U and θ̂ from the proof of Theorem 8.5 recovers the page's display
--   - encoding: ϱ ∈ [0, 1] → 0 ≤ ϱ; reason: ϱ ≤ 1 holds for unit vectors by Cauchy–Schwarz; same instances
--   - encoding: first column of U, p̃ ∈ ℝ^{d−1} → column 0, matrices over `Fin (n + 1)`, `ptilde U P`; reason: 0-based indices; same instances
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, Section 8.2.1, proof of Theorem 8.5, display following (8.16), p. 244 (PDF p. 264)

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_opNorm2
import Definitions.Def_WainwrightHDS_EigPert_ptilde
import Definitions.Def_WainwrightHDS_EigPert_psi

namespace WainwrightHDS.EigPert

open Matrix

/-- **Bound on `|Ψ(Δ̂; P)|` in the proof of Theorem 8.5.**
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, Section 8.2.1, proof of Theorem 8.5, display following (8.16), p. 244 (PDF p. 264):
"since `‖z̃‖₂ ≤ 1` and `|p̃₁₁| ≤ |||P̃|||₂`, we have
`|Ψ(Δ̂; P)| ≤ 2(1 − ϱ²)|||P̃|||₂ + 2ϱ√(1 − ϱ²)‖p̃‖₂`", with `ϱ = ⟨θ̂, θ*⟩ ∈ [0, 1]`,
`P̃ = UᵀPU` and `p̃` as in (8.11).

Let `U` be an orthogonal `d × d` matrix (`d = n + 1`) whose first column is `θ*`, let `P` be
symmetric, and let `θ̂` be a unit vector with `ϱ := ⟨θ̂, θ*⟩ ≥ 0`. Then
`|Ψ(θ̂ − θ*; P)| ≤ 2(1 − ϱ²)|||UᵀPU|||₂ + 2ϱ√(1 − ϱ²)‖p̃‖₂`.

**Formalization Note.** On the page `U` is the orthonormal matrix of eigenvectors of `Σ` with first
column `θ*` and `θ̂` is the maximal eigenvector of `Σ̂`; the display uses only that `U` is
orthogonal with first column `θ*` and that `θ̂` is a unit vector, which is what is assumed here.
`θ*` is a unit vector because it is a column of an orthogonal matrix; `ϱ ≤ 1` follows by
Cauchy–Schwarz. Indices 0-based: the first column is column `0`. -/
theorem abs_psi_le {n : ℕ} (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (θstar : EuclideanSpace ℝ (Fin (n + 1))) (hU0 : ∀ i, U i 0 = θstar i)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hP : P.IsHermitian)
    (θhat : EuclideanSpace ℝ (Fin (n + 1))) (hθhat : ‖θhat‖ = 1)
    (hρ : 0 ≤ inner ℝ θhat θstar) :
    |psi θstar P (θhat - θstar)| ≤
      2 * (1 - (inner ℝ θhat θstar) ^ 2) * opNorm2 (Uᵀ * P * U) +
        2 * inner ℝ θhat θstar * Real.sqrt (1 - (inner ℝ θhat θstar) ^ 2) * ‖ptilde U P‖ := by sorry

end WainwrightHDS.EigPert
