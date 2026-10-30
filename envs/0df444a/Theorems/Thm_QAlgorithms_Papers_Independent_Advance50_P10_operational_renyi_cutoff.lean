-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_operational_renyi_cutoff
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.operational_renyi_cutoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:38:26.793983+00:00
-- url     : https://prove2.me/theorems/e4628fb7-d660-4913-92cc-68c5699de3eb
-- title:
--   Theorem III.1: operational generalized cutoff rate
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $\rho,\sigma$ be density operators. A block test is an effect $0\le T_n\le I$ on $H^{\otimes n}$, with $\alpha_n=\operatorname{Tr}\rho^{\otimes n}(I-T_n)$ and $\beta_n=\operatorname{Tr}\sigma^{\otimes n}T_n$. For $r>0$, let $\overline h_r$ be the infimum of $\limsup_n n^{-1}\log_2\beta_n$ over test sequences satisfying $\limsup_n n^{-1}\log_2\alpha_n<-r$. At zero use the right limit. For $\kappa<0$, let $C_\kappa$ be the extended supremum of $r_0\ge0$ satisfying $\overline h_r\le\kappa(r_0-r)$ for every $r\ge0$. Then
--
--   $$C_\kappa(\rho\|\sigma)=\frac1{|\kappa|}S_{|\kappa|/(1+|\kappa|)}(\rho\|\sigma)=S_{1/(1+|\kappa|)}(\sigma\|\rho).$$
--
--   No support inclusion or distinctness is assumed. This gives the operational interpretation announced in the abstract.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 5, Theorem III.1: operational generalized cutoff rate

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

/-- Theorem III.1, PDF p.5, the operational main result announced on p.1.
The cutoff is defined through actual tests and the upper Hoeffding exponent. -/
theorem operational_renyi_cutoff {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : {A : Operator I // IsDensityMatrix A}) (k : ℝ) (hk : k < 0) :
    testingCutoff (fun n => n) (fun n => copies n rho.1) (fun n => copies n sigma.1) k =
      (((1 / |k| : ℝ) : EReal) * petzRelativeBits (|k| / (1 + |k|)) rho.1 sigma.1) ∧
    (((1 / |k| : ℝ) : EReal) * petzRelativeBits (|k| / (1 + |k|)) rho.1 sigma.1) =
      petzRelativeBits (1 / (1 + |k|)) sigma.1 rho.1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
