-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_measure_affinity_continuity
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.measure_affinity_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:42:13.12706+00:00
-- url     : https://prove2.me/theorems/55766ce1-2201-461d-8df6-3e8bb065f0da
-- title:
--   Lemma IV.1: affinity and continuity in the measure
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $K$ be a nonempty compact subset of the density operators on $H$, let $\mathcal M(K)$ be all Borel probability measures with the weak topology, and let $\mathcal M_f(K)$ be the finitely supported ones. Fix $0<\alpha\le2$, $\alpha
--   e1$, and put $f_{\alpha,\varepsilon}(p,\sigma)=\int_K S_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$ and $g_{\alpha,\varepsilon}(p,\sigma)=\int_K Q_\alpha(\rho\|\sigma+\varepsilon I)\,dp(\rho)$. Here $Q_\alpha=\operatorname{sign}(\alpha-1)\operatorname{Tr}\rho^\alpha B^{1-\alpha}$ on its finite domain and is $+\infty$ on support failure above one. The integrals are signed extended integrals; their negative parts are integrable. For every density operator $\sigma$ and $\varepsilon>0$,
--
--   $$p\longmapsto f_{\alpha,\varepsilon}(p,\sigma),\qquad p\longmapsto g_{\alpha,\varepsilon}(p,\sigma)$$
--
--   are affine and continuous on all of $\mathcal M(K)$. Affinity includes every weight in $[0,1]$. This supplies the law-variable hypotheses for minimax without restricting the law to a finite ensemble.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 6, Lemma IV.1: affinity and continuity in the measure

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

/-- Lemma IV.1, PDF p.6: affinity and weak continuity on all Borel probability laws,
for both the S and the signed Q objectives. -/
theorem measure_affinity_continuity {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (a : ℝ) (ha : 0 < a) (ha_two : a ≤ 2) (ha_one : a ≠ 1)
    (sigma : {A : Operator I // IsDensityMatrix A}) (e : ℝ) (he : 0 < e) :
    ∀ useQ : Bool,
      MeasureAffine (fun p => measureObjective K useQ a e p sigma) ∧
      Continuous (fun p => measureObjective K useQ a e p sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
