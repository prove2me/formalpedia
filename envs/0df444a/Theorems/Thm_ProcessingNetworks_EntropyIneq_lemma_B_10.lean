-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_lemma_B_10
-- name    : ProcessingNetworks.EntropyIneq.lemma_B_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:33.457112+00:00
-- url     : https://prove2.me/theorems/70963bfb-a262-46d4-a54f-53f785d43cba
-- title:
--   Lemma B.10 — flow-balance identity for the traffic equations
-- statement:
--   Throughout, $I\ge1$ is an integer, $\mathcal I=\{1,\dots,I\}$ is the set of classes, $\lambda\in\mathbb R^I_+$ is the vector of external arrival rates and $P$ is a non-negative $I\times I$ routing matrix with spectral radius $\rho(P)<1$; $P_{i0}:=1-\sum_{j\in\mathcal I}P_{ij}$, $\mathcal I_+=\mathcal I\cup\{0\}$, $\alpha:=(I-P')^{-1}\lambda$ is assumed positive and $\alpha_0:=1$ (Section B.4, (B.13)–(B.17)).
--
--   Set $d_0=1$ by convention and let $d_1,\dots,d_I$ be arbitrary real numbers. Then
--
--   $$
--   \sum_{i\in\mathcal I}d_i+\sum_{i\in\mathcal I}\lambda_i=\sum_{i\in\mathcal I}\alpha_i\sum_{j\in\mathcal I_+}P_{ij}\frac{d_j}{\alpha_j}+\sum_{i\in\mathcal I}d_i\frac{\lambda_i}{\alpha_i} .
--   $$
--
--   The identity is what makes the two vectors built from $d$ in the proof of Lemma B.13 have equal total mass, so that the unnormalized Pinsker inequality (Lemma B.12) applies.
--
--   **Formalization Note** The inner sum over $\mathcal I_+$ is the sum over the classes plus the class-$0$ term $P_{i0}\,d_0/\alpha_0=P_{i0}$.
--
--   Differences from the source:
--
--   - encoding: sums over 𝓘₊ = 𝓘 ∪ {0} with d₀ = α₀ = 1 → a sum over Fin I plus the explicit class-0 term outflow P i = P_{i0}; reason: class 0 is not an element of Fin I; same values
--   - encoding: ρ(P) < 1, ρ the largest modulus of an eigenvalue → RobustToDynamics.specRadius P < 1, the supremum of the moduli of the points of the spectrum of P over ℂ; reason: that spectrum is the set of complex eigenvalues, a finite nonempty set for I ≥ 1, so the supremum is the maximum
--   - encoding: α := (I − P′)⁻¹λ → traffic lam P, defined with Matrix.inv; reason: ρ(P) < 1 makes I − P′ invertible (Theorem F.1), so Matrix.inv is the true inverse
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, Lemma B.10, eq. (B.21), p.270 (PDF 286)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_SectionB4Assumptions
import Definitions.Def_ProcessingNetworks_EntropyIneq_outflow

namespace ProcessingNetworks.EntropyIneq

/-- **Lemma B.10** (Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix B §B.4, Lemma B.10, eq. (B.21), p.270 (PDF 286)). Under the standing
assumptions of Section B.4, with `α = (I − P′)⁻¹λ`, set `d₀ = 1` by convention and let
`d₁, …, d_I` be arbitrary. Then
`Σ_{i∈𝓘} dᵢ + Σ_{i∈𝓘} λᵢ = Σ_{i∈𝓘} αᵢ Σ_{j∈𝓘₊} P_{ij} d_j/α_j + Σ_{i∈𝓘} dᵢ λᵢ/αᵢ`.

**Formalization Note** `𝓘₊ = 𝓘 ∪ {0}`: the inner sum is `Σ_{j ∈ Fin I} P_{ij} d_j/α_j` plus the
class-0 term `P_{i0} · d₀/α₀ = outflow P i` (with `d₀ = α₀ = 1`). `d` is an arbitrary real vector. -/
theorem lemma_B_10 {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (hB4 : SectionB4Assumptions lam P) (d : Fin I → ℝ) :
    ∑ i, d i + ∑ i, lam i =
      ∑ i, traffic lam P i * (∑ j, P i j * (d j / traffic lam P j) + outflow P i) +
        ∑ i, d i * (lam i / traffic lam P i) := by sorry

end ProcessingNetworks.EntropyIneq
