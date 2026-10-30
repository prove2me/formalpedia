-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_quasi_relative_minimax
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.quasi_relative_minimax
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:47:46.009077+00:00
-- url     : https://prove2.me/theorems/87eebd95-8296-4745-becb-7afbf925b478
-- title:
--   Proposition IV.7: quasi-relative entropy minimax
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $K$ be a nonempty compact subset of the density operators on $H$, let $\mathcal M(K)$ be all Borel probability measures with the weak topology, and let $\mathcal M_f(K)$ be the finitely supported ones. Fix $0<\alpha\le2$, $\alpha
--   e1$, and put $f_{\alpha,\varepsilon}(p,\sigma)=\int_K S_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$ and $g_{\alpha,\varepsilon}(p,\sigma)=\int_K Q_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$. Here $Q_\alpha=\operatorname{sign}(\alpha-1)\operatorname{Tr}\rho^\alpha B^{1-\alpha}$ on its finite domain and is $+\infty$ on support failure above one. The integrals are signed extended integrals; their negative parts are integrable. The regularized and singular minimax chains of Propositions IV.3 and IV.4 hold with $g$ and $Q$ in place of $f$ and $S$. In particular, a limit $\sigma_0$ of regularized $g$-minimizers satisfies
--
--   $$\sup_p g_{\alpha,0}(p,\sigma_0)=\min_\sigma\sup_p g_{\alpha,0}(p,\sigma)=\sup_p\min_\sigma g_{\alpha,0}(p,\sigma)=\min_\sigma\sup_{\rho\in K}Q_\alpha(\rho\|\sigma)=\sup_{\rho\in K}Q_\alpha(\rho\|\sigma_0).$$
--
--   At positive perturbations every displayed supremum is a maximum, including the maximin, and a common minimizing centre exists. Both chains also hold for finite laws. This is the signed-quasi-entropy counterpart of the two minimax propositions.
--
--   Every selected regularized $Q$-minimizer family has a cluster centre along positive perturbations tending to zero; the singular chain holds for every such cluster centre.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 7, Proposition IV.7: quasi-relative entropy minimax

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

/-- Proposition IV.7, PDF p.7: both minimax results for the signed Q objective.
The singular limit centre exists for every selected Q-minimizer family, independently of f. -/
theorem quasi_relative_minimax {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (a : ℝ) (ha : 0 < a) (ha_two : a ≤ 2) (ha_one : a ≠ 1) :
    (∀ e : ℝ, 0 < e → ∃ sigma : {A : Operator I // IsDensityMatrix A},
      RegularizedMinimax (measureObjective K true a e) (pointObjective K true a e) sigma ∧
      RegularizedMinimax
        (fun p : {p : ProbabilityMeasure K // FiniteMeasureLaw p} => measureObjective K true a e p.1)
        (pointObjective K true a e) sigma) ∧
    (∀ centres : ℝ → {A : Operator I // IsDensityMatrix A}, CentreFamily K true a centres →
      (∃ sigma : {A : Operator I // IsDensityMatrix A}, CentreLimit centres sigma) ∧
      (∀ sigma : {A : Operator I // IsDensityMatrix A}, CentreLimit centres sigma →
        SingularMinimax (measureObjective K true a 0) (pointObjective K true a 0) sigma ∧
        SingularMinimax
          (fun p : {p : ProbabilityMeasure K // FiniteMeasureLaw p} => measureObjective K true a 0 p.1)
          (pointObjective K true a 0) sigma)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
