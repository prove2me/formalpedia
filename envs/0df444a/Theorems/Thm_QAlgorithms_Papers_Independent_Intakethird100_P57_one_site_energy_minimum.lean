-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_one_site_energy_minimum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.one_site_energy_minimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:12:53.70962+00:00
-- url     : https://prove2.me/theorems/4688806e-26ac-44c2-b54c-f1cb71c4052a
-- title:
--   Static updates: the one-site energy minimization is a generalized Rayleigh problem
-- statement:
--   Fix $N,D\ge1$, a valid nonzero RAGE vector, a site $k$, and a Hermitian finite-qubit Hamiltonian $H$. Freeze all data except the two site tensors at $k$. Let $x\in\mathbb C^{2D^2}$ contain their entries, let $L$ be the resulting physical-state linear map, and set $F=L^\dagger HL$, $G=L^\dagger L$. Then the updated raw vector is $Lx$ and, whenever $x^\dagger Gx>0$,
--
--   $$E(x)=\frac{x^\dagger Fx}{x^\dagger Gx}.$$
--
--   There exist $x_*$ with $x_*^\dagger Gx_*>0$ and a real $\lambda$ such that
--
--   $$Fx_*=\lambda Gx_*,\qquad E(x_*)=\lambda\le E(y)\quad(y^\dagger Gy>0).$$
--
--   The norm matrix may be singular; only vectors with nonzero physical image are admissible. The minimum is an attained one-site optimum.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 3, Static updates: the one-site energy minimization is a generalized Rayleigh problem

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.3, Static updates: the generalized Rayleigh reduction and an attained local
minimum. G may have a kernel. Eigenvectors are required to have positive G norm, preventing
common-kernel vectors from making arbitrary real numbers generalized eigenvalues. -/
theorem one_site_energy_minimum {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    (A : Tensors N D) (Gph : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (hv : rage A Gph V ≠ 0) (k : Fin N)
    (H : Matrix (Qubits N) (Qubits N) ℂ) (hH : H.IsHermitian) :
    let L := siteMap A Gph V k
    let F := L.conjTranspose * H * L
    let G := L.conjTranspose * L
    (∀ x : SiteCoordinates D → ℂ,
      rage (replaceSite A k x) Gph V = siteVector L x) ∧
    (∀ x : SiteCoordinates D → ℂ, 0 < (rageSiteQuadratic G x).re →
      rayleighEnergy H (rage (replaceSite A k x) Gph V) =
        (rageSiteQuadratic F x).re / (rageSiteQuadratic G x).re) ∧
    (∃ (x : SiteCoordinates D → ℂ) (lam : ℝ),
      0 < (rageSiteQuadratic G x).re ∧ F.mulVec x = (lam : ℂ) • G.mulVec x ∧
      (rageSiteQuadratic F x).re / (rageSiteQuadratic G x).re = lam ∧
      (∀ y : SiteCoordinates D → ℂ, 0 < (rageSiteQuadratic G y).re →
        lam ≤ (rageSiteQuadratic F y).re / (rageSiteQuadratic G y).re)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
