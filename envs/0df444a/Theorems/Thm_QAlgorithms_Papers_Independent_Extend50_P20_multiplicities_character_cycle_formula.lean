-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_multiplicities_character_cycle_formula
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.multiplicities_character_cycle_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:08:51.012992+00:00
-- url     : https://prove2.me/theorems/568fea6e-3ed6-4c4c-bddf-8832dbdea922
-- title:
--   Character cycle formula for squared multiplicities
-- statement:
--   Let $d\ge1$ and $N\ge0$. Let $m_\nu$ be the actual multiplicities in the tensor-factor permutation representation of $S_N$ on $(\mathbb C^d)^{\otimes N}$. Let $\ell_N(\sigma)$ count all disjoint cycles of $\sigma\in S_N$, including fixed points. Then
--
--   $$\sum_{\nu\vdash N,\,h(\nu)\le d}m_\nu^2=\frac1{N!}\sum_{\sigma\in S_N}d^{2\ell_N(\sigma)}.$$
--
--   For $N=0$, the empty shape has multiplicity one and the empty permutation has zero cycles, so both sides are one. This is a character expression for the squared-multiplicity sum.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 22, Proposition 11 / Eq. (105)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Proposition 11, PDF p.22, Eq.(105). Actual physical Schur dimensions
appear on the left, and every fixed point is counted on the right. N=0
is included: the empty tensor space and empty permutation each contribute one. -/
theorem multiplicities_character_cycle_formula (d N : ℕ) (hd : 0 < d) :
    multiplicitySquares d N =
      (∑ pi : Equiv.Perm (Fin N), (d : ℝ)^(2*cycleCount pi)) /
        (N.factorial : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
