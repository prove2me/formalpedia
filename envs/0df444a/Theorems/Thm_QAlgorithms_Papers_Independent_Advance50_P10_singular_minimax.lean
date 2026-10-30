-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_singular_minimax
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.singular_minimax
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:45:14.299495+00:00
-- url     : https://prove2.me/theorems/09dcf37e-c5a1-4f3b-b9a7-d8f694e8fd5d
-- title:
--   Proposition IV.4: singular minimax via centre limits
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $K$ be a nonempty compact subset of the density operators on $H$, let $\mathcal M(K)$ be all Borel probability measures with the weak topology, and let $\mathcal M_f(K)$ be the finitely supported ones. Fix $0<\alpha\le2$, $\alpha
--   e1$, and put $f_{\alpha,\varepsilon}(p,\sigma)=\int_K S_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$ and $g_{\alpha,\varepsilon}(p,\sigma)=\int_K Q_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$. Here $Q_\alpha=\operatorname{sign}(\alpha-1)\operatorname{Tr}\rho^\alpha B^{1-\alpha}$ on its finite domain and is $+\infty$ on support failure above one. The integrals are signed extended integrals; their negative parts are integrable. Choose, for every $\varepsilon>0$, a minimizing centre $\sigma_\varepsilon$ for $\sup_{p\in\mathcal M(K)}f_{\alpha,\varepsilon}(p,\sigma)$. Such a family has at least one cluster centre along positive perturbations tending to zero. For every such cluster centre, let $\sigma_0$ be the limit of $\sigma_{\varepsilon_k}$ along a positive sequence $\varepsilon_k\to0$. Then
--
--   $$\sup_{p\in\mathcal M(K)} f_{\alpha,0}(p,\sigma_0)=\min_{\sigma\in\mathcal S(H)}\sup_{p\in\mathcal M(K)}f_{\alpha,0}(p,\sigma)=\sup_{p\in\mathcal M(K)}\min_{\sigma\in\mathcal S(H)}f_{\alpha,0}(p,\sigma)=\min_{\sigma\in\mathcal S(H)}\sup_{\rho\in K}S_\alpha(\rho\|\sigma)=\sup_{\rho\in K}S_\alpha(\rho\|\sigma_0).$$
--
--   Every printed minimum is attained. The same chain holds when law suprema are restricted to $\mathcal M_f(K)$. This identifies the singular minimax value at a centre obtained by regularization.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 6, Proposition IV.4: singular minimax via centre limits

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

/-- Proposition IV.4, PDF pp.6–7: the singular minimax chain at a limit of
regularized minimizing centres. Existence of a limit centre is also concluded. -/
theorem singular_minimax {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (a : ℝ) (ha : 0 < a) (ha_two : a ≤ 2) (ha_one : a ≠ 1)
    (centres : ℝ → {A : Operator I // IsDensityMatrix A}) (hcentres : CentreFamily K false a centres)
    : (∃ sigma : {A : Operator I // IsDensityMatrix A}, CentreLimit centres sigma) ∧
    (∀ sigma : {A : Operator I // IsDensityMatrix A}, CentreLimit centres sigma →
      SingularMinimax (measureObjective K false a 0) (pointObjective K false a 0) sigma ∧
      SingularMinimax
        (fun p : {p : ProbabilityMeasure K // FiniteMeasureLaw p} =>
          measureObjective K false a 0 p.1)
        (pointObjective K false a 0) sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
