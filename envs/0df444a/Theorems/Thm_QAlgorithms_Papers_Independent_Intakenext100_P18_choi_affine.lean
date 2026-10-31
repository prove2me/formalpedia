-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_choi_affine
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.choi_affine
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:22:59.216741+00:00
-- url     : https://prove2.me/theorems/db93d0e0-6edc-42b8-b3b5-eed7e2c18821
-- title:
--   Normalized Choi affine correspondence
-- statement:
--   Let $d\ge1$, let $P_+=|\Phi_d\rangle\langle\Phi_d|$, where $|\Phi_d\rangle=d^{-1/2}\sum_{i=0}^{d-1}|ii\rangle$, and let a channel mean a completely positive trace-preserving complex-linear map on $d\times d$ matrices. The computed reference-first Choi map and its inverse are
--
--   $$J(\Lambda)=(\operatorname{id}\otimes\Lambda)(P_+),\qquad \Lambda_\rho(X)=d\operatorname{Tr}_{\rm ref}[(X^{\mathsf T}\otimes I)\rho].$$
--
--   They are inverse bijections between channels and positive trace-one operators $\rho$ with output partial trace $\operatorname{Tr}_{\rm out}\rho=I/d$. The map $J$ preserves every convex combination, so this is an affine correspondence.
--
--   This identifies channels with normalized bipartite states having the specified first marginal. It does not assert physical recovery of an arbitrary channel by teleportation.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 4, §II, unnumbered: normalized state-channel affine correspondence

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF pp.3--4, (2)--(9): the actual normalized Choi map is an affine
bijection with the displayed computed inverse. The first marginal is I/d.
No claim of physical channel recovery by teleportation is part of this result. -/
theorem choi_affine (d : ℕ) (hd : 0 < d) :
    (∀ E : Superop (Fin d) (Fin d), IsChannel E →
      IsDensityMatrix (choiState E) ∧
      traceRight (choiState E) = ((1 / (d : ℝ) : ℝ) : ℂ) • 1 ∧
      choiInverse d (choiState E) = E) ∧
    (∀ rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      IsDensityMatrix rho → traceRight rho = ((1 / (d : ℝ) : ℝ) : ℂ) • 1 →
      IsChannel (choiInverse d rho) ∧ choiState (choiInverse d rho) = rho) ∧
    (∀ E G : Superop (Fin d) (Fin d), IsChannel E → IsChannel G →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      choiState (fun X => (t : ℂ) • E X + ((1 - t : ℝ) : ℂ) • G X) =
        (t : ℂ) • choiState E + ((1 - t : ℝ) : ℂ) • choiState G) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
