-- Prove2me | Theorems.Thm_WainwrightHDS_EigPert_pca_basic_inequality
-- name    : WainwrightHDS.EigPert.pca_basic_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:27:48.171693+00:00
-- url     : https://prove2.me/theorems/26b33217-b618-475f-b61a-a23f1645ec02
-- title:
--   Lemma 8.6 — PCA basic inequality $\nu(1 - \langle\widehat\theta, \theta^*\rangle^2) \le |\Psi(\widehat\Delta; P)|$
-- statement:
--   Let $\Sigma$ be a real symmetric positive semidefinite $d \times d$ matrix, $d \ge 2$, with eigenvalues $\gamma_1(\Sigma) \ge \gamma_2(\Sigma) \ge \dots$, eigengap
--
--   $$
--   \nu = \gamma_1(\Sigma) - \gamma_2(\Sigma) > 0,
--   $$
--
--   and maximal unit eigenvector $\theta^*$. Let $P$ be a symmetric $d \times d$ matrix and $\widehat\Sigma = \Sigma + P$. Let $C \subseteq \mathbb{S}^{d-1}$ be a set of unit vectors with $\theta^* \in C$ (so that $\theta^*$ maximizes $\langle\theta, \Sigma\theta\rangle$ over $C$), and let $\widehat\theta \in C$ maximize $\langle\theta, \widehat\Sigma\theta\rangle$ over $C$. Then, with $\widehat\Delta = \widehat\theta - \theta^*$ and $\Psi$ as in (8.13),
--
--   $$
--   \nu\bigl(1 - \langle\widehat\theta, \theta^*\rangle^2\bigr) \;\le\; \bigl|\Psi(\widehat\Delta; P)\bigr| .
--   $$
--
--   This is the basic inequality for PCA: it converts optimality of $\widehat\theta$ into a bound on the angle between $\widehat\theta$ and $\theta^*$. The case $C = \mathbb{S}^{d-1}$ is used for Theorem 8.5; general $C$ is used for sparse PCA (Section 8.3).
--
--   **Formalization Note** Indices are 0-based: $\gamma_1 = $ `gamma S hS.1 0`, $\gamma_2 = $ `gamma S hS.1 1`, and $d = n + 2$. No sign condition on $\langle\widehat\theta, \theta^*\rangle$ is imposed; both sides are invariant under $\widehat\theta \mapsto -\widehat\theta$.
--
--   Differences from the source:
--   - reading: θ* and θ̂ maximize ⟨θ, Σθ⟩ and ⟨θ, Σ̂θ⟩ over C (8.14) → θ* is the maximal unit eigenvector of Σ (standing setup of Section 8.2.1) and θ* ∈ C, θ̂ ∈ C maximizes ⟨θ, Σ̂θ⟩ over C; reason: the proof uses Γθ* = 0, i.e. that θ* is the top eigenvector; the literal reading "θ* any maximizer over C" is false (Σ = diag(2, 1), P = 0, C = {(1/2, √3/2), (−1/2, √3/2)}: both points maximize, and ν(1 − ⟨θ̂, θ*⟩²) = 3/4 > 0 = |Ψ|)
--   - reading: P = Σ̂ − Σ with Σ̂ unspecified → P symmetric; reason: the perturbation of Sections 8.1.2–8.2.1 and Theorem 8.5 is a symmetric matrix (P ∈ S^{d×d}); the Lemma's Σ is positive semidefinite by the standing assumption of Section 8.2.1
--   - encoding: d × d with γ₂ defined → matrices over `Fin (n + 2)`, γ_j as 0-based `gamma`; reason: γ₂(Σ) only exists for d ≥ 2; same instances
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, p. 243 (PDF p. 263), Lemma 8.6, Eq. (8.15), with the programs (8.14); standing setup Section 8.2.1, p. 242 (PDF p. 262)

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_gamma
import Definitions.Def_WainwrightHDS_EigPert_IsMaxEigenvector
import Definitions.Def_WainwrightHDS_EigPert_psi

namespace WainwrightHDS.EigPert

/-- **Lemma 8.6 (PCA basic inequality), Eq. (8.15).**
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, p. 243 (PDF p. 263). Setup (8.14): for a subset `C ⊆ S^{d−1}`, `θ*` and `θ̂` maximize
`⟨θ, Σθ⟩` and `⟨θ, Σ̂θ⟩` over `C`; "Given a matrix `Σ` with eigengap `ν > 0`, the error
`Δ̂ = θ̂ − θ*` is bounded as `ν (1 − ⟨θ̂, θ*⟩²) ≤ |Ψ(Δ̂; P)|`", where `P = Σ̂ − Σ`.

Let `Σ` be positive semidefinite (`d = n + 2 ≥ 2`) with eigengap `ν = γ₁(Σ) − γ₂(Σ) > 0` and
maximal unit eigenvector `θ*`; let `P` be symmetric and `Σ̂ = Σ + P`. Let `C` be a subset of the unit
sphere containing `θ*`, and let `θ̂ ∈ C` maximize `⟨θ, Σ̂θ⟩` over `C`. Then
`ν (1 − ⟨θ̂, θ*⟩²) ≤ |Ψ(θ̂ − θ*; P)|`.

**Formalization Note.** Reading of "θ* maximizes `⟨θ, Σθ⟩` over `C`": `θ*` is the maximal
eigenvector of `Σ` from the standing setup of Section 8.2.1 and `θ* ∈ C` (then it does maximize
over `C`); the literal reading "any maximizer over `C`" is false. No sign condition on
`⟨θ̂, θ*⟩` is imposed. Indices 0-based: `γ₁ = gamma Σ _ 0`, `γ₂ = gamma Σ _ 1`. -/
theorem pca_basic_inequality {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (hS : S.PosSemidef) (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hP : P.IsHermitian)
    (C : Set (EuclideanSpace ℝ (Fin (n + 2)))) (hC : C ⊆ {v | ‖v‖ = 1})
    (hθstarC : θstar ∈ C) (θhat : EuclideanSpace ℝ (Fin (n + 2))) (hθhatC : θhat ∈ C)
    (hθhat_max : ∀ θ ∈ C, inner ℝ θ (Matrix.toEuclideanLin (S + P) θ) ≤
      inner ℝ θhat (Matrix.toEuclideanLin (S + P) θhat)) :
    (gamma S hS.1 0 - gamma S hS.1 1) * (1 - (inner ℝ θhat θstar) ^ 2) ≤
      |psi θstar P (θhat - θstar)| := by sorry

end WainwrightHDS.EigPert
