-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_lemma_B_14
-- name    : ProcessingNetworks.EntropyIneq.lemma_B_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:49.449083+00:00
-- url     : https://prove2.me/theorems/6b96a2e8-1637-4693-aa62-3e2dc433367e
-- title:
--   Lemma B.14 — the minimum $\kappa(\alpha,\delta)$ away from $d=e$ is attained and positive
-- statement:
--   Let $I\ge1$ and let $P$ be a non-negative $I\times I$ matrix with spectral radius $\rho(P)<1$, with $P_{i0}=1-\sum_jP_{ij}$. Given a constant $\delta>0$ and a vector $\alpha\in\mathbb R^I$ with all components strictly positive, consider
--
--   $$
--   \kappa(\alpha,\delta)\equiv\min_{d\in\mathbb R^I_+:\ |d-e|\ge\delta}\ \sum_{i\in\mathcal I}\alpha_i\Big|d_i-\sum_{j\in\mathcal I_+}P_{ij}d_j\Big| ,
--   $$
--
--   where $d_0=1$, $e$ is the vector of ones and $|x|=\sum_i|x_i|$. The minimum is attained, and the optimal value $\kappa(\alpha,\delta)$ is strictly positive.
--
--   The objective vanishes only at the fixed point $d=e$ of $d\mapsto Pd+P_{\cdot0}$; the lemma quantifies how far it stays from $0$ outside a neighbourhood of $e$, which the entropy Lyapunov argument of Section 10.5 needs.
--
--   **Formalization Note** "The minimum is strictly positive" is stated as: some $\kappa>0$ is the least element of the set of objective values over the feasible set. Here $\alpha$ is an arbitrary positive vector, not the traffic vector.
--
--   Differences from the source:
--
--   - generalization: P the matrix of Section B.4, together with λ ∈ ℝ^I_+ such that (I − P′)⁻¹λ > 0 → any I ≥ 1 and any non-negative P with ρ(P) < 1; no λ; reason: λ does not occur in the lemma; the section's P is such a matrix
--   - encoding: min … (B.32), the optimal value is strictly positive → ∃ κ, IsLeast (objective '' feasible set) κ ∧ 0 < κ; reason: states both attainment (the book writes min) and positivity
--   - encoding: Σ_{j∈𝓘₊} P_ij d_j with d₀ = 1 → a sum over Fin I plus the explicit class-0 term outflow P i = P_{i0}; reason: class 0 is not an element of Fin I; same values
--   - encoding: ρ(P) < 1, ρ the largest modulus of an eigenvalue → RobustToDynamics.specRadius P < 1, the supremum of the moduli of the points of the spectrum of P over ℂ; reason: that spectrum is the set of complex eigenvalues, a finite nonempty set for I ≥ 1, so the supremum is the maximum
--   - encoding: |d − e| ≥ δ, with |x| = Σᵢ |xᵢ| (Guide, p.xv) → δ ≤ ∑ i, |d i - 1|; reason: the book's ℓ¹ norm written out
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, Lemma B.14, eq. (B.32), p.272 (PDF 288)

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_ProcessingNetworks_EntropyIneq_outflow

namespace ProcessingNetworks.EntropyIneq

/-- **Lemma B.14** (Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix B §B.4, Lemma B.14, eq. (B.32), p.272 (PDF 288)). Let `I ≥ 1` and `P` be a
non-negative `I × I` matrix with spectral radius `< 1` (the section's `P`). Given a constant
`δ > 0` and a vector `α ∈ ℝ^I` with all components strictly positive, consider
`κ(α, δ) ≡ min_{d ∈ ℝ^I_+ : |d − e| ≥ δ} Σ_{i∈𝓘} αᵢ |dᵢ − Σ_{j∈𝓘₊} P_{ij} d_j|`, where `d₀ = 1` by
convention and `e` is the vector of ones. The minimum is attained and the optimal value
`κ(α, δ)` is strictly positive.

**Formalization Note** `|x| = Σᵢ |xᵢ|` is the book's ℓ¹ norm (Guide, p.xv). `Σ_{j∈𝓘₊} P_{ij} d_j`
is `Σ_{j ∈ Fin I} P_{ij} d_j + outflow P i` (`d₀ = 1`). "min … is strictly positive" is stated as:
some `κ` is the least element of the set of objective values over the feasible set, and `κ > 0`.
`α` is an arbitrary positive vector, not the traffic vector, and the section's `λ` plays no role. -/
theorem lemma_B_14 {I : ℕ} (hI : 0 < I) (P : Matrix (Fin I) (Fin I) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hρ : RobustToDynamics.specRadius P < 1)
    (α : Fin I → ℝ) (hα : ∀ i, 0 < α i) (δ : ℝ) (hδ : 0 < δ) :
    ∃ κ : ℝ,
      IsLeast ((fun d : Fin I → ℝ => ∑ i, α i * |d i - (∑ j, P i j * d j + outflow P i)|) ''
          {d : Fin I → ℝ | (∀ i, 0 ≤ d i) ∧ δ ≤ ∑ i, |d i - 1|}) κ ∧
        0 < κ := by sorry

end ProcessingNetworks.EntropyIneq
