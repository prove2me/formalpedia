-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_continuousLogDensityEquipartition
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.continuousLogDensityEquipartition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:46:17.775432+00:00
-- url     : https://prove2.me/theorems/6743b030-af00-4f30-a131-a056d7b1b29c
-- title:
--   §3 remarks: continuous log-density concentration suffices for equipartition
-- statement:
--   Let strictly positive trace-one density matrices $\sigma^N$ define $\omega^N(A)=\operatorname{Tr}(\sigma^NA)$ on nonzero finite-dimensional complex Hilbert spaces. Put $A^N=N^{-1}\log\sigma^N$. Suppose that for every continuous complex-valued function $F$ on $\mathbb R$,
--
--   $$\omega^N(F(A^N))-F(\omega^N(A^N))\longrightarrow0.$$
--
--   Then, with $B^N=A^N-\omega^N(A^N)I$, for every $\delta>0$,
--
--   $$\lim_{N\to\infty}\frac1N\log\omega^N\!\left(1_{[-\delta,\delta]}(B^N)\right)=0.$$
--
--   Zero spectral mass has logarithm $-\infty$. No uniform operator-norm bound on $A^N$ is imposed, and its centering mean may vary with $N$. This continuous-test criterion supplies asymptotic equipartition.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 9, §3 remarks: continuous log-density concentration suffices for equipartition

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, (3.4)-(3.5): continuous tests concentrating about the moving mean
of scaled log density suffice for AEP. No uniform bound on log density is assumed. -/
theorem continuousLogDensityEquipartition {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S)
    (hrho : IsStateSequence rho) (hpositive : ∀ n, (rho n).PosDef)
    (hcontinuous : ∀ F : ℝ → ℂ, Continuous F →
      Tendsto (fun n => traceExpectation (rho n) (spectralFunction F (scaledLogDensity rho n)) -
        F ((traceExpectation (rho n) (scaledLogDensity rho n)).re)) atTop (𝓝 (0 : ℂ))) :
    asymptoticEquipartition rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
