-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_faithful_centre_infima
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.faithful_centre_infima
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:46:00.956275+00:00
-- url     : https://prove2.me/theorems/cba33f1c-cd54-4b61-be47-c8426f8d74c3
-- title:
--   Remark IV.5: faithful-centre infimum restriction
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $K$ be a nonempty compact subset of the density operators on $H$, let $\mathcal M(K)$ be all Borel probability measures with the weak topology, and let $\mathcal M_f(K)$ be the finitely supported ones. Fix $0<\alpha\le2$, $\alpha
--   e1$, and put $f_{\alpha,\varepsilon}(p,\sigma)=\int_K S_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$ and $g_{\alpha,\varepsilon}(p,\sigma)=\int_K Q_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$. Here $Q_\alpha=\operatorname{sign}(\alpha-1)\operatorname{Tr}\rho^\alpha B^{1-\alpha}$ on its finite domain and is $+\infty$ on support failure above one. The integrals are signed extended integrals; their negative parts are integrable. Write $\mathcal S(H)_{++}$ for the invertible density operators. For each $p\in\mathcal M(K)$,
--
--   $$\min_{\sigma\in\mathcal S(H)} f_{\alpha,0}(p,\sigma)=\inf_{\sigma\in\mathcal S(H)_{++}} f_{\alpha,0}(p,\sigma).$$
--
--   The same replacement holds for the minimum of $\sup_{p\in\mathcal M(K)}f_{\alpha,0}(p,\sigma)$, with either all or finitely supported laws, and for the minimum of $\sup_{\rho\in K}S_\alpha(\rho\|\sigma)$. The original minima are attained; the restricted infima need not be. This allows faithful centres in infimum formulas without imposing attainment there.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 7, Remark IV.5: faithful-centre infimum restriction

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Remark IV.5, PDF p.7: each of the three centre minima in (28)–(29) can
be restricted to invertible densities as an infimum; no restricted attainment is asserted. -/
theorem faithful_centre_infima {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (a : ℝ) (ha : 0 < a) (ha_two : a ≤ 2) (ha_one : a ≠ 1) :
    (∀ p : ProbabilityMeasure K, ReachesMinimum (measureObjective K false a 0 p)) ∧
    ReachesMinimum (fun sigma : {A : Operator I // IsDensityMatrix A} =>
      ⨆ p : ProbabilityMeasure K, measureObjective K false a 0 p sigma) ∧
    ReachesMinimum (fun sigma : {A : Operator I // IsDensityMatrix A} => ⨆ rho : K, pointObjective K false a 0 sigma rho) ∧
    ReachesMinimum (fun sigma : {A : Operator I // IsDensityMatrix A} =>
      ⨆ p : {p : ProbabilityMeasure K // FiniteMeasureLaw p}, measureObjective K false a 0 p.1 sigma) ∧
    (∀ p : ProbabilityMeasure K,
      (⨅ sigma : {A : Operator I // IsDensityMatrix A}, measureObjective K false a 0 p sigma) =
      ⨅ sigma : {sigma : {A : Operator I // IsDensityMatrix A} // sigma.1.PosDef}, measureObjective K false a 0 p sigma.1) ∧
    ((⨅ sigma : {A : Operator I // IsDensityMatrix A}, ⨆ p : ProbabilityMeasure K, measureObjective K false a 0 p sigma) =
      ⨅ sigma : {sigma : {A : Operator I // IsDensityMatrix A} // sigma.1.PosDef},
        ⨆ p : ProbabilityMeasure K, measureObjective K false a 0 p sigma.1) ∧
    ((⨅ sigma : {A : Operator I // IsDensityMatrix A},
        ⨆ p : {p : ProbabilityMeasure K // FiniteMeasureLaw p}, measureObjective K false a 0 p.1 sigma) =
      ⨅ sigma : {sigma : {A : Operator I // IsDensityMatrix A} // sigma.1.PosDef},
        ⨆ p : {p : ProbabilityMeasure K // FiniteMeasureLaw p}, measureObjective K false a 0 p.1 sigma.1) ∧
    ((⨅ sigma : {A : Operator I // IsDensityMatrix A}, ⨆ rho : K, pointObjective K false a 0 sigma rho) =
      ⨅ sigma : {sigma : {A : Operator I // IsDensityMatrix A} // sigma.1.PosDef},
        ⨆ rho : K, pointObjective K false a 0 sigma.1 rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
