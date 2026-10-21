-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_goal_reduction
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.goal_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:06:08.158669+00:00
-- url     : https://prove2.me/theorems/7d5c41c6-a2a0-4b87-b279-ff62c718089d
-- title:
--   §IV: positive invariant goal functions reduce to likelihood
-- statement:
--   Let $U$ be a strongly continuous projective unitary action of a unimodular Lie group on a complete complex Hilbert space, with two-sided Haar measure $dg$, and let $K$ be a compact stabilizer subgroup. Let $h:G\to[0,\infty)$ be a measurable $K$-biinvariant lift of an invariant goal, integrable with $H=\int_Gh(g)dg>0$. Define the weak weighted-conjugation map
--
--   $$\mathcal M_h(\rho)=H^{-1}\int_Gh(g)U_g^\dagger\rho U_g\,dg.$$
--
--   This map on trace class is complex linear, completely positive, and trace preserving. It sends density operators to density operators. For every normalized positive covariant seed $\Xi$, the score integrand is integrable and
--
--   $$\overline s_h(\Xi)=H\operatorname{Tr}[\Xi\mathcal M_h(\rho)].$$
--
--   Consequently the two objectives order all admissible seeds identically. The identically zero goal has score zero for every seed. The reduction may produce a mixed state.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 4, §IV: positive invariant goal functions reduce to likelihood

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

/-- PDF p.4: positive invariant goals reduce exactly to likelihood on M(rho).
Nonnegative and positive-total-weight are the reading needed for the printed CPTP claim. -/
theorem goal_reduction (hLie : RealLie G) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (h : G → ℝ) (hh : Goal R K h) :
    TraceClassCPTP (goalMap R h) ∧
    (∀ rho : PhysicalOperator H, HilbertDensity rho → HilbertDensity (goalMap R h rho) ∧
      WeakIntegral R.dg (fun g => ((h g / (∫ t, h t ∂(R.dg)) : ℝ) : ℂ) •
        (representedOperator R g⁻¹).comp (rho.comp (ContinuousLinearMap.adjoint (representedOperator R g⁻¹))))
        (goalMap R h rho) ∧
      ∀ A : PhysicalOperator H, Seed R K A →
        Integrable (fun g => h g * mixedLikelihood (conjugatedSeed R A g) rho) R.dg ∧
        invariantGoalScore R h rho A = (∫ g, h g ∂(R.dg)) * mixedLikelihood A (goalMap R h rho)) ∧
    (∀ rho A B : PhysicalOperator H, HilbertDensity rho → Seed R K A → Seed R K B →
      (invariantGoalScore R h rho A ≤ invariantGoalScore R h rho B ↔
        mixedLikelihood A (goalMap R h rho) ≤ mixedLikelihood B (goalMap R h rho))) ∧
    (∀ rho A : PhysicalOperator H, invariantGoalScore R (fun _ => 0) rho A = 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
