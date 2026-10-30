-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_regularized_minimax
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.regularized_minimax
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:44:19.587763+00:00
-- url     : https://prove2.me/theorems/0126612d-3760-4275-bcf0-1124ac943a0a
-- title:
--   Proposition IV.3: regularized minimax and attainment
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $K$ be a nonempty compact subset of the density operators on $H$, let $\mathcal M(K)$ be all Borel probability measures with the weak topology, and let $\mathcal M_f(K)$ be the finitely supported ones. Fix $0<\alpha\le2$, $\alpha
--   e1$, and put $f_{\alpha,\varepsilon}(p,\sigma)=\int_K S_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$ and $g_{\alpha,\varepsilon}(p,\sigma)=\int_K Q_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$. Here $Q_\alpha=\operatorname{sign}(\alpha-1)\operatorname{Tr}\rho^\alpha B^{1-\alpha}$ on its finite domain and is $+\infty$ on support failure above one. The integrals are signed extended integrals; their negative parts are integrable. For every $\varepsilon>0$ there exists a density operator $\sigma_\varepsilon$ such that
--
--   $$\max_{p\in\mathcal M(K)}f_{\alpha,\varepsilon}(p,\sigma_\varepsilon)=\min_\sigma\max_{p\in\mathcal M(K)}f_{\alpha,\varepsilon}(p,\sigma)=\max_{p\in\mathcal M(K)}\min_\sigma f_{\alpha,\varepsilon}(p,\sigma)=\min_\sigma\max_{\rho\in K}S_\alpha(\rho\|\sigma+\varepsilon I)=\max_{\rho\in K}S_\alpha(\rho\|\sigma_\varepsilon+\varepsilon I).$$
--
--   All state minima range over $\mathcal S(H)$ and all displayed extrema attain their values. The same chain holds with maxima over $\mathcal M_f(K)$, with the same centre. This produces actual regularized centres.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 6, Proposition IV.3: regularized minimax and attainment

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

/-- Proposition IV.3, PDF p.6: the full regularized minimax chain with every
printed minimum and maximum attained, both for all laws and for finite laws. -/
theorem regularized_minimax {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (a : ℝ) (ha : 0 < a) (ha_two : a ≤ 2) (ha_one : a ≠ 1)
    (e : ℝ) (he : 0 < e) :
    ∃ sigma : {A : Operator I // IsDensityMatrix A},
      RegularizedMinimax (measureObjective K false a e) (pointObjective K false a e) sigma ∧
      RegularizedMinimax
        (fun p : {p : ProbabilityMeasure K // FiniteMeasureLaw p} =>
          measureObjective K false a e p.1)
        (pointObjective K false a e) sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
