-- Prove2me | Theorems.Thm_WainwrightHDS_EigPert_max_eigenvector_perturbation_bound
-- name    : WainwrightHDS.EigPert.max_eigenvector_perturbation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:29:06.295409+00:00
-- url     : https://prove2.me/theorems/5ab64e0d-60cc-4a14-9e18-f2a0ef7338f1
-- title:
--   Theorem 8.5 — perturbation bound $\|\widehat\theta - \theta^*\|_2 \le 2\|\tilde p\|_2 / (\nu - 2|||P|||_2)$ for the maximal eigenvector
-- statement:
--   Let $\Sigma$ be a real symmetric positive semidefinite $d \times d$ matrix, $d \ge 2$, with eigenvalues $\gamma_1(\Sigma) \ge \gamma_2(\Sigma) \ge \dots \ge \gamma_d(\Sigma)$, maximal unit eigenvector $\theta^* \in \mathbb{S}^{d-1}$, and eigengap
--
--   $$
--   \nu = \gamma_1(\Sigma) - \gamma_2(\Sigma) > 0 .
--   $$
--
--   Let $U$ be an orthonormal $d \times d$ matrix whose columns are eigenvectors of $\Sigma$ and whose first column is $\theta^*$, and for a matrix $P$ let $\tilde p \in \mathbb{R}^{d-1}$ be the off-diagonal block of $\widetilde P = U^\top P U$ as in (8.11). Let $P$ be any symmetric $d \times d$ matrix with
--
--   $$
--   |||P|||_2 < \frac{\nu}{2},
--   $$
--
--   and let $\widehat\Sigma = \Sigma + P$. Then:
--
--   1. $\widehat\Sigma$ has a maximal unit eigenvector;
--   2. it is unique up to sign: any two maximal unit eigenvectors $v, w$ of $\widehat\Sigma$ satisfy $v = w$ or $v = -w$;
--   3. every maximal unit eigenvector $\widehat\theta$ of $\widehat\Sigma$ with $\langle\widehat\theta, \theta^*\rangle \ge 0$ satisfies
--
--   $$
--   \|\widehat\theta - \theta^*\|_2 \;\le\; \frac{2\,\|\tilde p\|_2}{\nu - 2\,|||P|||_2} . \tag{8.12}
--   $$
--
--   The theorem is the deterministic core of the analysis of principal component analysis: applied with $\Sigma$ the population covariance and $\widehat\Sigma$ the sample covariance, it turns a bound on $|||\widehat\Sigma - \Sigma|||_2$ into a bound on the error of the estimated leading principal direction (Corollary 8.7 for the spiked ensemble). The requirement $|||P|||_2 < \nu/2$ cannot be relaxed to $\le$: for $\Sigma = \mathrm{diag}(2, 1)$ and $P = \mathrm{diag}(-\tfrac12, \tfrac12)$, $\widehat\Sigma = \tfrac32 I_2$ has no unique maximal eigenvector.
--
--   **Formalization Note** Indices are 0-based: $\gamma_1 = $ `gamma S hS.1 0`, $\gamma_2 = $ `gamma S hS.1 1`, the first column of $U$ is column `0`, and $d = n + 2$. A maximal eigenvector is a unit vector $v$ with $\widehat\Sigma v = \gamma_1(\widehat\Sigma) v$. The bound holds for every admissible $U$.
--
--   Differences from the source:
--   - reading: "Σ̂ has a unique maximal eigenvector θ̂ satisfying (8.12)" → (1) a maximal unit eigenvector exists, (2) it is unique up to sign, (3) (8.12) holds for every maximal unit eigenvector θ̂ with ⟨θ̂, θ*⟩ ≥ 0; reason: a unit eigenvector is determined only up to sign, and the proof (p. 243) fixes the sign so that ϱ = ⟨θ̂, θ*⟩ ∈ [0, 1]; for the other sign (8.12) is false (P = 0, θ̂ = −θ* gives ‖θ̂ − θ*‖₂ = 2 > 0)
--   - reading: U an orthonormal matrix with the eigenvectors of Σ as its columns (8.11) → U orthogonal, every column an eigenvector of Σ, first column θ*, and the bound for every such U; reason: the proof (p. 244) uses that U's first column is θ*; the book does not fix the remaining columns, and the statement is made for every admissible choice
--   - encoding: d × d with γ₂(Σ) and p̃ ∈ ℝ^{d−1} → matrices over `Fin (n + 2)`, 0-based `gamma`, column 0; reason: γ₂ and p̃ only exist for d ≥ 2; same instances
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, p. 243 (PDF p. 263), Theorem 8.5, Eq. (8.12); setup Section 8.2.1 and Eq. (8.11), p. 242 (PDF p. 262)

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_opNorm2
import Definitions.Def_WainwrightHDS_EigPert_gamma
import Definitions.Def_WainwrightHDS_EigPert_IsMaxEigenvector
import Definitions.Def_WainwrightHDS_EigPert_ptilde

namespace WainwrightHDS.EigPert

open Matrix

/-- **Theorem 8.5 (perturbation bound for the maximal eigenvector), Eq. (8.12).**
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, p. 243 (PDF p. 263), with the setup of Section 8.2.1 and (8.11), p. 242 (PDF p. 262):
"Consider a positive semidefinite matrix `Σ` with maximum eigenvector `θ* ∈ S^{d−1}` and eigengap
`ν = γ₁(Σ) − γ₂(Σ) > 0`. Given any matrix `P ∈ S^{d×d}` such that `|||P|||₂ < ν/2`, the perturbed
matrix `Σ̂ := Σ + P` has a unique maximal eigenvector `θ̂` satisfying the bound
`‖θ̂ − θ*‖₂ ≤ 2‖p̃‖₂ / (ν − 2|||P|||₂)`."

Here `d = n + 2 ≥ 2`, `U` is an orthogonal matrix whose columns are eigenvectors of `Σ` and whose
first column is `θ*`, and `p̃` is the off-diagonal block of `UᵀPU` (8.11). Conclusion:
(1) `Σ + P` has a maximal unit eigenvector; (2) it is unique up to sign; (3) every maximal unit
eigenvector `θ̂` of `Σ + P` with `⟨θ̂, θ*⟩ ≥ 0` satisfies (8.12).

**Formalization Note.** "Unique maximal eigenvector" is read as unique up to sign (a unit
eigenvector is never unique otherwise), and the bound is stated for the representative with
`⟨θ̂, θ*⟩ ≥ 0`, as in the proof's "without loss of generality … `ϱ ∈ [0, 1]`" (p. 243); for the
other sign the bound fails already at `P = 0`. Indices 0-based: `γ₁ = gamma Σ _ 0`,
`γ₂ = gamma Σ _ 1`, the first column of `U` is column `0`. -/
theorem max_eigenvector_perturbation_bound {n : ℕ}
    (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (n + 2)) ℝ)
    (hUeig : ∀ j, ∃ μ : ℝ, S *ᵥ (fun i => U i j) = μ • (fun i => U i j))
    (hU0 : ∀ i, U i 0 = θstar i)
    (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hP : P.IsHermitian)
    (hsmall : opNorm2 P < (gamma S hS.1 0 - gamma S hS.1 1) / 2) :
    (∃ θhat, IsMaxEigenvector (S + P) (hS.1.add hP) θhat) ∧
    (∀ v w, IsMaxEigenvector (S + P) (hS.1.add hP) v →
      IsMaxEigenvector (S + P) (hS.1.add hP) w → v = w ∨ v = -w) ∧
    (∀ θhat, IsMaxEigenvector (S + P) (hS.1.add hP) θhat → 0 ≤ inner ℝ θhat θstar →
      ‖θhat - θstar‖ ≤
        2 * ‖ptilde U P‖ / (gamma S hS.1 0 - gamma S hS.1 1 - 2 * opNorm2 P)) := by sorry

end WainwrightHDS.EigPert
