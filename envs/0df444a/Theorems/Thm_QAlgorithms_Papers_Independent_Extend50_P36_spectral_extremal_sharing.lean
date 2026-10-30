-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_spectral_extremal_sharing
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.spectral_extremal_sharing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:13:45.635026+00:00
-- url     : https://prove2.me/theorems/370a6d1e-77d5-4acb-af7a-05acd7e2692a
-- title:
--   Appendix B, unnumbered main construction: extremal sharing from the largest eigenspace
-- statement:
--   Let $d\ge2$ be an integer. Write $\rho_W(\psi)$ for the $d$-dimensional Werner state with swap expectation $\psi\in[-1,1]$, and $\rho_I(\phi)$ for the isotropic state with $\phi=dF\in[0,d]$, where $F$ is its overlap with the normalized maximally entangled vector. A joining state is a positive semidefinite operator of trace one having the specified ordered pair marginals.For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   Fix $m,n\ge1$. On the actual $(m+n)$-qudit register set $H=-(mn)^{-1}\sum_{i\in L,j\in R}V_{ij}$, where $V_{ij}$ swaps the chosen left and right sites. This is Hermitian. Its real spectrum has a greatest element $r\in[0,1]$. Let $P$ be the orthogonal projector onto the entire $r$ eigenspace. Its trace is strictly positive, and
--   $$w=P/\operatorname{Tr}P\quad\text{has every left-right marginal }\rho_W(-r).$$
--   Moreover $C_W(-r)=r$, and any $m$-$n$ sharable physical Werner state has concurrence at most $r$. Thus the top eigenvalue is precisely the attained maximal concurrence.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 17, Appendix B, unnumbered main construction: extremal sharing from the largest eigenspace

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Appendix B, PDF p.17: the normalized projector onto the entire top eigenspace
is an extremal sharing state, and the largest eigenvalue is the maximal concurrence. -/
theorem spectral_extremal_sharing (d m n : ℕ) (hd : 2 ≤ d) (hm : 0 < m) (hn : 0 < n) :
    let H := sharingHamiltonian d m n
    let r := maximalRealEigenvalue H
    H.IsHermitian ∧ IsGreatest (realEigenvalues H) r ∧
    0 ≤ r ∧ r ≤ 1 ∧
    0 < (fullEigenkernelProjector H r).trace.re ∧
    Shares (extremalSharingState d m n) (wernerSwapState d (-r)) ∧
    wernerConcurrence (-r) = r ∧
    (∀ psi : ℝ, -1 ≤ psi → psi ≤ 1 → Sharable m n (wernerSwapState d psi) →
      wernerConcurrence psi ≤ r) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
