-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_td_fluctuations
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.td_fluctuations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:48:51.49073+00:00
-- url     : https://prove2.me/theorems/1551d2fe-55be-4e81-9206-6ec7d5b88fdf
-- title:
--   TD Evans–Searles symmetry
-- statement:
--   Let finite quantum systems $Q_m$ with faithful states satisfy TD on an open symmetric interval $I\supset[0,1]$. Write $e_t(s)=\lim_m e_{mt}(s)$ and $P_t$ for the thermodynamic FCS. Suppose every $Q_m$ has a common real orthonormal representation of its Hamiltonian and initial state. For all fixed $t>0$ and $s\in I$,
--
--   $$e_t(s)=e_t(1-s)=\log\int e^{-ts\phi}\,dP_t(\phi),\qquad (\phi\mapsto-\phi)_*P_t=e^{-t\phi}dP_t(\phi).$$
--
--   The last equality is a measure identity, not a pointwise density formula.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 25, TD Evans–Searles symmetry

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- TD Evans--Searles symmetry, all equivalent formulations on PDF p.25,
arXiv:1109.3804v2, (4.14). The measure identity is reflection/pushforward. -/
theorem td_fluctuations (Q : ℕ → FiniteSystem) (I : Set ℝ) (hTD : HasTD Q I)
    (hTRI : ∀ m, IsFiniteTRI (Q m).H (Q m).omega) :
    ∀ t : ℝ, 0 < t →
      (∀ s ∈ I, tdEntropic Q t s = tdEntropic Q t (1 - s) ∧
        tdEntropic Q t s = Real.log (∫ phi : ℝ, Real.exp (-t * s * phi) ∂tdFCS Q t)) ∧
      Measure.map (fun phi : ℝ => -phi) (tdFCS Q t) =
        (tdFCS Q t).withDensity (fun phi => ENNReal.ofReal (Real.exp (-t * phi))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
