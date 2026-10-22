-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_depolarizingExplicitEvaluations
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.depolarizingExplicitEvaluations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:55:57.004338+00:00
-- url     : https://prove2.me/theorems/3a6ba823-6093-4d86-b471-425343399541
-- title:
--   Explicit entropy, norm, and Holevo values with attainment
-- statement:
--   Let $d\ge2$ and $-1/(d^2-1)\le\lambda\le1$. Write $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$. All states are positive semidefinite with trace one; all information quantities use natural logarithms with $0\log0=0$. Here $S_{\min}$ is the infimum of output von Neumann entropy over all input states, $\nu_p$ is the supremum of the positive Schatten $p$-norm over those states, and $\chi^*$ is the supremum of the output Holevo information over all finite normalized input ensembles. Put $a=\lambda+(1-\lambda)/d$ and $b=(1-\lambda)/d$. Then
--
--   $$S_{\min}(\Delta_\lambda)=-a\log a-(d-1)b\log b,\qquad \nu_p(\Delta_\lambda)=\bigl(a^p+(d-1)b^p\bigr)^{1/p}\ (p\ge1),\qquad \chi^*(\Delta_\lambda)=\log d-S_{\min}(\Delta_\lambda).$$
--
--   For every orthonormal basis, its rank-one projectors with uniform weights $1/d$ form a normalized ensemble of average $I/d$ attaining $\chi^*$. Each of these pure input states attains the minimum output entropy and every indicated maximal output norm. These formulas evaluate all three measures rather than only a scalar capacity surrogate.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 4, Unnumbered evaluations (9)–(11) and optimal orthonormal ensemble

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

namespace QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0204172v2, PDF pp.3-4, (9)-(11): all three evaluations,
with basis-ensemble attainment and pure-output attainment of the entropy/norm extrema. -/
theorem depolarizingExplicitEvaluations {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1) :
    (minimumOutputEntropy (depolarizing d (1 - lam))).toReal = depolarizingEntropy d lam ∧
    (∀ p : ℝ, 1 ≤ p → maximumOutputPNorm (depolarizing d (1 - lam)) p = depolarizingNormFactor d lam p) ∧
    holevoQuantity (depolarizing d (1 - lam)) = Real.log d - (minimumOutputEntropy (depolarizing d (1 - lam))).toReal ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      IsLaw (basisProb d) ∧
      (∀ k, IsDensityMatrix (basisProjector (U : Matrix (Fin d) (Fin d) ℂ) k)) ∧
      (∑ k, (basisProb d k : ℂ) • basisProjector (U : Matrix (Fin d) (Fin d) ℂ) k) =
        (d : ℂ)⁻¹ • 1 ∧
      Real.log 2 * QAlgorithms.Papers.Independent.Claimed50.P43.basisHolevo (d := d) (by omega) (1 - lam) U =
        holevoQuantity (depolarizing d (1 - lam)) ∧
      ∀ k, entropy (depolarizing d (1 - lam) (basisProjector (U : Matrix (Fin d) (Fin d) ℂ) k)) =
          (minimumOutputEntropy (depolarizing d (1 - lam))).toReal ∧
        ∀ p : ℝ, 1 ≤ p → schatten p
          (depolarizing d (1 - lam) (basisProjector (U : Matrix (Fin d) (Fin d) ℂ) k)) =
          maximumOutputPNorm (depolarizing d (1 - lam)) p := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
