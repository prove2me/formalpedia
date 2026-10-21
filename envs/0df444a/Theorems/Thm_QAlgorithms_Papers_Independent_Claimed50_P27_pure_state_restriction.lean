-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_pure_state_restriction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.pure_state_restriction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:20:34.342995+00:00
-- url     : https://prove2.me/theorems/427eba7a-2a10-4d49-9d1c-a87fee7a48fe
-- title:
--   Restriction of the attaining postprocessor to a pure state
-- statement:
--   Let $d\ge2$, let $|\psi\rangle$ be a unit vector in $\mathbb C^d$, and initialize the memory of the postprocessing channel $B$ from Eq. (9) in $|+\rangle$. Let $P_+$ project onto the symmetric subspace of $\mathbb C^d\otimes\mathbb C^d$, whose dimension is $d_+=d(d+1)/2$. Then
--
--   $$B(|\psi\rangle\langle\psi|\otimes|+\rangle\langle+|)=\frac d{d_+}P_+(|\psi\rangle\langle\psi|\otimes I)P_+.$$
--
--   This identifies the pure-state-cloning restriction of the unitary cloner's postprocessor. The separate optimization theorem calling this an optimal pure-state cloner is attributed by the paper to Werner [19]; no new state-cloning figure of merit is asserted here.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 3, Paragraph after Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.3: the restriction of B to a pure input and memory |+>.
This is the displayed identity; the separate optimal-state-cloning criterion
is not introduced, since the paper attributes that optimization to [19]. -/
theorem pure_state_restriction (d : ℕ) (hd : 2 ≤ d)
    (psi : EuclideanSpace ℂ (Fin d)) (hpsi : IsState psi) :
    optimalPost d (Matrix.kronecker (pureDensity psi) (pureDensity (ket true))) =
      (((d : ℝ) / sectorDim d true : ℝ) : ℂ) •
        (sectorProjector d true *
          Matrix.kronecker (pureDensity psi) (1 : Matrix (Fin d) (Fin d) ℂ) *
            sectorProjector d true) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
