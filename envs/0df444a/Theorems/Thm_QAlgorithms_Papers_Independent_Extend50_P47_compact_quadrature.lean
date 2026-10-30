-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_compact_quadrature
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.compact_quadrature
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:18:45.32344+00:00
-- url     : https://prove2.me/theorems/2b208f8f-3621-41ee-8a91-81161130faba
-- title:
--   Remark 2: finite quadrature for compact-group tests
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity.
--
--   For a continuous ordinary unitary representation of a compact Lie group on a nonzero finite register, normalized Haar average Π has a finite convex-combination expression Σj pj U(gj). Preparing Σj sqrt(pj)|j⟩, controlling U(gj), and projecting back gives probability Tr(Πρ) for a density input (pure-state form as printed); no efficient construction of p or its state preparation is asserted.
--
--   $$
--   \Pi=\int_G U(g)\,d\mu(g)=\sum_{i=1}^N p_iU(g_i),\qquad p_i\ge0,\quad\sum_i p_i=1,\quad p_{\rm acc}=\operatorname{Tr}(\Pi\rho).
--   $$
--
--   $\mu$ is normalized Haar measure on a compact finite-dimensional real Lie group, and $U$ is continuous. The controlled test prepares $\sum_i\sqrt{p_i}|i\rangle$ and projects back to that same control state.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 12, Remark 2: finite quadrature for compact-group tests

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF pp.12–13, Remark 2: exact finite probability quadrature of the Haar
average of a continuous finite-dimensional unitary representation. No synthesis
or preparation complexity is asserted. Haar measure is normalized to total mass one. -/
theorem compact_quadrature [Nonempty S] {H E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group H] [TopologicalSpace H] [T2Space H] [SecondCountableTopology H]
    [ChartedSpace E H] [LieGroup (𝓘(ℝ, E)) ∞ H]
    [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (mu : Measure H) [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu]
    (U : H →* Matrix.unitaryGroup S ℂ)
    (hcont : Continuous (fun g => (U g : Mat S))) :
    ∃ (n : ℕ) (g : Fin n → H) (p : Fin n → ℝ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      (∫ h, (U h : Mat S) ∂mu) = ∑ i, (p i : ℂ) • (U (g i) : Mat S) ∧
      ∀ rho : Mat S, IsDensityMatrix rho →
        controlReturnProbability (∑ i, (p i : ℂ) • (U (g i) : Mat S)) rho =
          effectProb (∫ h, (U h : Mat S) ∂mu) rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
