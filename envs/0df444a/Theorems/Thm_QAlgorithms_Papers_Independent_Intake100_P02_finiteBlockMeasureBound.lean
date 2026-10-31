-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P02_finiteBlockMeasureBound
-- name    : QAlgorithms.Papers.Independent.Intake100.P02.finiteBlockMeasureBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:50:55.848857+00:00
-- url     : https://prove2.me/theorems/03a2cf82-f60f-497b-aaa9-7fc844c71262
-- title:
--   Finite-block normalization–continuity bound
-- statement:
--   Let $n,k,a,b$ be positive integers. On two key registers of dimension $k$ and shield registers of dimensions $a,b$, let $\tau$ be a normalized shield density and $U_i$ arbitrary shield unitaries. The private target is
--
--   $$\phi=\frac1k\sum_{i,j=0}^{k-1}|ii\rangle\langle jj|\otimes U_i\tau U_j^\dagger.$$
--
--   Let $\rho$ be any normalized output density on the same total dimension $d=k^2ab$, and put $R_n=\log_2(k)/n$. Let $E$ be one nonnegative functional family over all such dimensions, normalized by $E(\phi)\ge\log_2 k$ for every private target and satisfying $|E(\rho)-E(\sigma)|\le g(\epsilon)\log_2 d+h(\epsilon)$ for normalized states at unhalved trace-norm distance at most $\epsilon$, on its specified interval $0\le\epsilon<r\le1$, $r>0$. If $\|\rho-\phi\|_1\le\epsilon<r$, then
--
--   $$R_n\le\frac{E(\rho)+g(\epsilon)\log_2 d+h(\epsilon)}{n}.$$
--
--   This is the source’s output-state inequality and hence applies to every actual finite-dimensional protocol output, including end-to-end outputs. Maximally entangled targets use trivial shields. No uniform shield bound, simulation, or capacity definition is required; only the two stated functional properties are used.
-- source:
--   Theory of channel simulation and bounds for private communication, arXiv:1711.09909v3, PDF p. 15, VIII A, Eq. (129): finite-block bound for a generic measure

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P02

open Filter MeasureTheory QAlgorithms

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal)

/-- arXiv:1711.09909v3, PDF p.15, (129): bound for every normalized finite
output close to a private target in unhalved trace norm. This applies to actual
mean outputs of both point-to-point and end-to-end protocols. Only normalization
and continuity are required, using the actual dimension, without simulation or
a uniform bound on shields. Maximally entangled targets have trivial shields. -/
theorem finiteBlockMeasureBound (E : FiniteTargetFunctional)
    (n k a b : ℕ) (hn : 0 < n) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (KeyRegister k a b) (KeyRegister k a b) ℂ)
    (hrho : IsDensityMatrix rho)
    (shield : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hshield : IsDensityMatrix shield)
    (U : Fin k → Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (eps : ℝ) (heps_nonnegative : 0 ≤ eps) (heps_small : eps < E.radius)
    (hclose : traceNorm (rho - privateTarget shield U) ≤ eps) :
    finiteKeyRate k n ≤
      (E.value k a b rho +
        E.g eps * Real.logb 2 ((k : ℝ) ^ 2 * (a : ℝ) * (b : ℝ)) + E.h eps) /
        (n : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P02

end
