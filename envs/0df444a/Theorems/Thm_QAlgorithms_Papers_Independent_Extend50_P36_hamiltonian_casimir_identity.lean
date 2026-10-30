-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_hamiltonian_casimir_identity
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.hamiltonian_casimir_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:14:27.288989+00:00
-- url     : https://prove2.me/theorems/64089ace-d00f-4bdd-aa84-dd7eae91280f
-- title:
--   Appendix B, unnumbered: Hamiltonian identity in collective Casimirs
-- statement:
--   Let $d\ge2$ and $m,n\ge1$ be integers. Choose $d^2-1$ Hermitian traceless $d\times d$ matrices $\lambda_\alpha$ with $\operatorname{Tr}(\lambda_\alpha\lambda_\beta)=\delta_{\alpha\beta}$. For each group $S=L,R,L\cup R$, define the embedded collective quadratic Casimir $C_S=\sum_\alpha(\sum_{i\in S}\lambda_\alpha^{(i)})^2$ on the common full tensor register. Then
--   $$-\frac1{mn}\sum_{i\in L,j\in R}V_{ij}=\frac{C_L+C_R-C_{L\cup R}}{2mn}-\frac Id.$$
--   Here $V_{ij}$ are actual cross-group swaps. This fixes both the generator normalization and the sign of the interaction.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 17, Appendix B, unnumbered: Hamiltonian identity in collective Casimirs

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Eq.(B1), PDF p.17: identity in embedded collective Casimirs with the source's
Tr(lambda_alpha lambda_beta)=delta normalization. -/
theorem hamiltonian_casimir_identity (d m n : ℕ) (hd : 2 ≤ d) (hm : 0 < m) (hn : 0 < n)
    (L : Fin (d*d-1) → Op (Fin d)) (hL : NormalizedGenerators d L) :
    sharingHamiltonian d m n =
      (1/(2*(m : ℂ)*(n : ℂ))) •
        (collectiveCasimir true false L+collectiveCasimir false true L-collectiveCasimir true true L) -
      (1/(d : ℂ)) • 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
