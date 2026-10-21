-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_ssaEquality_iff_blocks
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.ssaEquality_iff_blocks
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:57:21.966308+00:00
-- url     : https://prove2.me/theorems/820baff8-2273-44bc-9b40-3b3237cad5a5
-- title:
--   Theorem 6: structure of equality in strong subadditivity (original seed)
-- statement:
--   Let $A,B,C$ be nonzero finite-dimensional complex Hilbert spaces and let $\rho_{ABC}$ be a density operator. All marginal operators are obtained by partial trace and all entropies $S$ use logarithms to base two. Then
--
--   $$S(\rho_{AB})+S(\rho_{BC})-S(\rho_{ABC})-S(\rho_B)=0$$
--
--   if and only if there are finitely many nonzero spaces $L_j,R_j$, a unitary $W:H_B\to\bigoplus_j(L_j\otimes R_j)$, nonnegative weights $q_j$ summing to one, and density operators $\alpha_j$ on $A\otimes L_j$ and $\beta_j$ on $R_j\otimes C$, such that
--
--   $$(1_A\otimes W\otimes1_C)\rho_{ABC}(1_A\otimes W^*\otimes1_C)=\bigoplus_j q_j\alpha_j\otimes\beta_j.$$
--
--   The decomposition covers all of $B$, including the kernel of its marginal; zero weights are allowed. It characterizes the finite-dimensional short quantum Markov states. **Formalization Note** The equality is expressed by reconstruction through the adjoint block inclusions of $W$, which is equivalent to the displayed transported equality.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 4, Theorem 6: structure of equality in strong subadditivity (original seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted interfaces, inspected in the pinned library.

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI)

/-- PDF p.4, Theorem 6, proof p.5: exact finite-dimensional characterization of SSA equality. -/
theorem ssaEquality_iff_blocks {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hrho : IsDensityMatrix rho) :
    quantumCMI rho = 0 ↔ HasMarkovBlocks rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
