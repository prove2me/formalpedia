-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_phase_pure_mixed
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.phase_pure_mixed
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:23:45.958984+00:00
-- url     : https://prove2.me/theorems/00516d9f-53c7-4804-9847-4c58a8389e30
-- title:
--   §VI: phase-pure mixed-state extension
-- statement:
--   Use a finite complete orthogonal decomposition into square-integrable irreducible components for a strongly continuous projective unitary representation of a unimodular Lie group. Choose unit vectors $\psi_\mu$ in these components with $\langle\psi_\mu,I_{\mu\nu}\psi_\nu\rangle=0$ for distinct equivalent indices. Let $\rho$ be a positive trace-one operator supported on their span. Suppose real phases $\theta_\mu$ satisfy $\rho_{\mu\nu}=e^{i(\theta_\mu-\theta_\nu)}|\rho_{\mu\nu}|$, where $\rho_{\mu\nu}=\langle\psi_\mu,\rho\psi_\nu\rangle$. Let $K$ be a compact subgroup fixing $\rho$. With $b_\mu$ the formal coefficients, the seed formed from $\eta=\sum_\mu e^{i\theta_\mu}\sqrt{b_\mu^{-1}}\psi_\mu$, and then probability-Haar averaged over $K$, is positive and normalized and attains
--
--   $$L_{\max}=\sum_{\mu,\nu}\frac{|\rho_{\mu\nu}|}{\sqrt{b_\mu b_\nu}}\le\sum_{\rho_{\mu\mu}>0}b_\mu^{-1}.$$
--
--   The bound applies to every competing normalized covariant seed. The result does not require $\rho$ to have rank one or factorized matrix-entry magnitudes.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 7, §VI: phase-pure mixed-state extension

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P30

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)

open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (R : CovariantHilbertData G H)

variable {M : Type*} [DecidableEq M]

variable (D : Components R M)

/-- PDF p.7: phase-pure finite-component mixed states. Distinct-equivalent-pair
orthogonality is corrected as in Eq.(18); rho need not have rank one. -/
theorem phase_pure_mixed [Fintype M] (hLie : RealLie G)
    (v : M → H) (hv : ∀ i, D.I i i (v i) = v i ∧ ‖v i‖ = 1)
    (ho : ∀ i j, i ≠ j → D.equiv.r i j → inner ℂ (v i) (D.I i j (v j)) = 0)
    (rho : PhysicalOperator H) (hrho : HilbertDensity rho) (hsupp : SupportedOn rho v)
    (theta : M → ℝ)
    (hphase : ∀ i j, inner ℂ (v i) (rho (v j)) =
      Complex.exp (Complex.I * (theta i - theta j : ℝ)) * ‖inner ℂ (v i) (rho (v j))‖)
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hfix : ∀ k : K, conjugatedSeed R rho k = rho) (S : StabilizerHaar K) :
    let eta := ∑ i, (Complex.exp (Complex.I * (theta i : ℂ)) *
      (Real.sqrt ((formalCoefficient R D i)⁻¹) : ℂ)) • v i
    let A := stabilize R S (InnerProductSpace.rankOne ℂ eta eta)
    Seed R K A ∧
      mixedLikelihood A rho =
        ∑ i, ∑ j, ‖inner ℂ (v i) (rho (v j))‖ /
          Real.sqrt (formalCoefficient R D i * formalCoefficient R D j) ∧
      (∀ B : PhysicalOperator H, Seed R K B → mixedLikelihood B rho ≤ mixedLikelihood A rho) ∧
      ENNReal.ofReal (mixedLikelihood A rho) ≤
        ∑ i, if inner ℂ (v i) (rho (v i)) = 0 then 0 else
          ENNReal.ofReal ((formalCoefficient R D i)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
