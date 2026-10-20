-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_tensorProductConcaveHull
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.tensorProductConcaveHull
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:38:19.114056+00:00
-- url     : https://prove2.me/theorems/020c823f-7b27-419e-8b70-1fa2a89a1d5f
-- title:
--   Tensor-product measurements and the concave hull
-- statement:
--   Let $\rho^{AB}$ be a finite-dimensional bipartite density matrix and $R\ge0$. Let $C_{\rm prod}(\rho,R)$ be the operational one-way common-randomness capacity when Alice’s initial measurement is a tensor product of possibly different one-copy POVMs, with free stochastic classical postprocessing. Let $\widetilde D^{(1)}$ be the concave hull of $D^{(1)}$, defined by finite convex combinations with nonnegative component rates and mean rate $R$. Then
--
--   $$C_{\rm prod}(\rho,R)-R=\widetilde D^{(1)}(\rho,R).$$
--
--   For the normalized $L$-copy excess curves, both original and concavified curves converge to the same unrestricted operational excess:
--
--   $$\lim_{L\to\infty}D^{(L)}(\rho,R)=\lim_{L\to\infty}\widetilde D^{(L)}(\rho,R)=D(\rho,R).$$
--
--   This distinguishes repeating one POVM from deterministic time sharing among different product measurements. Universal finite-rate additivity remains open.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 18, §3, final paragraph: tensor-product measurement trade-off

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section QuantumStatements

variable {A B A2 B2 : Type} [Fintype A] [Fintype B] [Fintype A2] [Fintype B2]
  [DecidableEq A] [DecidableEq B] [DecidableEq A2] [DecidableEq B2]
  [Nonempty A] [Nonempty B] [Nonempty A2] [Nonempty B2]

/-- PDF p.18, final paragraph: time-shared product measurements give the concave hull;
concavified block curves and original block curves have the same operational limit. -/
theorem tensorProductConcaveHull (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (R : ℝ) (hR : 0 ≤ R) :
    productCapacity rho R - R = concaveHull (fixedExcess rho) R ∧
    Tendsto (fun L : ℕ => concaveHull (blockExcess rho L) R) atTop (nhds (crExcess rho R)) ∧
    Tendsto (fun L : ℕ => blockExcess rho L R) atTop (nhds (crExcess rho R)) := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
