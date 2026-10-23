-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P59_maximalOrthogonalSymmetry
-- name    : QAlgorithms.Papers.Independent.Information100.P59.maximalOrthogonalSymmetry
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:26:07.342287+00:00
-- url     : https://prove2.me/theorems/3b8cea24-96a3-4123-a46d-272e37934f67
-- title:
--   Proposition 3.6: Maximal orthogonal Bloch symmetry group
-- statement:
--   Let $\mathcal W_{\mathrm{GKLS}}$ be the cone of qubit generators with a Hamiltonian term and finitely many jump dissipators. An invertible real matrix $T\in\mathrm{GL}(3,\mathbb R)$ acts on affine Bloch generators by $(Q,b)\mapsto(TQT^{-1},Tb)$. If this transformation maps the cone onto itself, then
--
--   $$T^{\mathsf T}T=I.$$
--
--   For the extremal damping generator $D=(\operatorname{diag}(-1/2,-1/2,-1),-e_z)$, conjugation by $T=2I$ gives a generator outside that cone, hence violates conditional complete positivity.
--
--   This identifies the maximal ambient linear symmetry group; preservation here means equality of cones, not merely inclusion.
-- source:
--   Lie-Wedge Stratification and Pure-State Stabilizability in Single- Channel Qubit Control, arXiv:2610.00046v1, PDF p. 11, Proposition 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P59

attribute [local instance 100] LieRing.ofAssociativeRing

/-- arXiv:2610.00046v1 PDF p.11, Proposition 3.6. Preservation means equality of
cones (an automorphism), as required by the source's use of the inverse transformation. -/
theorem maximalOrthogonalSymmetry (T : Mat) (hT : T.det ≠ 0) :
    ((blochConjugate T '' {X : Block | IsGKLS X}) = {X : Block | IsGKLS X} →
      T.transpose * T = 1) ∧
    ¬ IsGKLS (blochConjugate (2 • (1 : Mat)) dampingBlock) := by sorry

end QAlgorithms.Papers.Independent.Information100.P59

end
