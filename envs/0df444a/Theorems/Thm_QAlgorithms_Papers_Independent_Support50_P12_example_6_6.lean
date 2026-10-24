-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_example_6_6
-- name    : QAlgorithms.Papers.Independent.Support50.P12.example_6_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:45:02.961097+00:00
-- url     : https://prove2.me/theorems/7e1d1e04-1022-4f5e-b2a0-3aec64c475a1
-- title:
--   Example 6.6
-- statement:
--   Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   In the diagonal algebra on $\mathbb C^3$, set $\rho=\operatorname{diag}(2/3,1/3,0)$ and $\sigma=\operatorname{diag}(1/6,1/3,1/2)$, and let $\Phi$ merge the first two diagonal entries into the first. This map is CPTP, $\Phi(\rho)=\operatorname{diag}(1,0,0)$, $\Phi(\sigma)=\operatorname{diag}(1/2,0,1/2)$, and for every real $\alpha$ the input and output trace overlaps are $(2+4^\alpha)/6$ and $2^{\alpha-1}$. Therefore
--
--   $$C(\Phi(\rho)\Vert\Phi(\sigma))=S_0(\Phi(\rho)\Vert\Phi(\sigma))=\log2=S_0(\rho\Vert\sigma)=C(\rho\Vert\sigma),$$
--
--   but $\Phi_\sigma^*(\Phi(\rho))=\operatorname{diag}(1/3,2/3,0)
--   e\rho$. No stochastic map recovers both inputs. This is the explicit endpoint-preservation counterexample.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 31, Example 6.6

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Example 6.6, PDF p.31: explicit CPTP Chernoff-preserving but irreversible pair.
The printed '-log psi' typo is not copied, since psi is already logarithmic. -/
theorem example_6_6 :
    AlgebraCompletelyPositive (diagonalAlgebra (Fin 3)) merge ∧ AlgebraTracePreserving (diagonalAlgebra (Fin 3)) merge ∧
    AlgebraDensity (diagonalAlgebra (Fin 3)) exampleRho ∧ AlgebraDensity (diagonalAlgebra (Fin 3)) exampleSigma ∧
    merge exampleRho = Matrix.diagonal ![(1 : ℂ), 0, 0] ∧
    merge exampleSigma = Matrix.diagonal ![(1 / 2 : ℂ), 0, 1 / 2] ∧
    (∀ a : ℝ, tr (supportPower exampleRho a * supportPower exampleSigma (1 - a)) =
      (2 + Real.rpow 4 a) / 6) ∧
    (∀ a : ℝ, tr (supportPower (merge exampleRho) a * supportPower (merge exampleSigma) (1 - a)) =
      Real.rpow 2 (a - 1)) ∧
    chernoff (merge exampleRho) (merge exampleSigma) = (Real.log 2 : EReal) ∧
    chernoff exampleRho exampleSigma = (Real.log 2 : EReal) ∧
    petzRenyi 0 (merge exampleRho) (merge exampleSigma) = (Real.log 2 : EReal) ∧
    petzRenyi 0 exampleRho exampleSigma = (Real.log 2 : EReal) ∧
    petz exampleSigma merge (merge exampleRho) = Matrix.diagonal ![(1 / 3 : ℂ), 2 / 3, 0] ∧
    petz exampleSigma merge (merge exampleRho) ≠ exampleRho ∧
    ¬ Reversible (diagonalAlgebra (Fin 3)) (diagonalAlgebra (Fin 3)) merge exampleRho exampleSigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
