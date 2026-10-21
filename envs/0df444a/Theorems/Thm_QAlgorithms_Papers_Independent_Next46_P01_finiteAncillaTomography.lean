-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P01_finiteAncillaTomography
-- name    : QAlgorithms.Papers.Independent.Next46.P01.finiteAncillaTomography
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:29:09.706416+00:00
-- url     : https://prove2.me/theorems/0cf6f180-1ec3-41d3-a9b7-d60c8597bc5c
-- title:
--   Finite ancilla tomography recovers the entropic functional
-- statement:
--   Let $\mathcal K$ be a nonzero finite-dimensional complex Hilbert space, $H=H^*$ a Hamiltonian, $\omega>0$ a density matrix, and $\nu$ any density matrix. Let $\rho$ be a qubit density matrix, written in the ordered basis $(+,-)$, with $\rho_{+-}\ne0$. For $t\in\mathbb R$ and $\alpha\in i\mathbb R$, put $\omega_u=e^{-iuH}\omega e^{iuH}$, $\sigma_z=\operatorname{diag}(1,-1)$, and
--   $$
--   \widehat H_\alpha=e^{(\alpha/2)(\log\omega)\otimes\sigma_z}(H\otimes1)e^{-(\alpha/2)(\log\omega)\otimes\sigma_z},\qquad
--   F_{\nu,t}^{\rm ancilla}(\alpha)=\operatorname{tr}(\nu\omega^{-\alpha/2}\omega_{-t}^{\alpha}\omega^{-\alpha/2}).
--   $$
--   Then the reduced ancilla density is
--   $$
--   \operatorname{tr}_{\mathcal K}\!\left(e^{-it\widehat H_\alpha}(\nu\otimes\rho)e^{it\widehat H_\alpha}\right)
--   =\begin{pmatrix}\rho_{++}&F_{\nu,t}^{\rm ancilla}(\alpha)\rho_{+-}\\\overline{F_{\nu,t}^{\rm ancilla}(\alpha)}\rho_{-+}&\rho_{--}\end{pmatrix}.
--   $$
--   Thus the ancilla coherence determines the finite-time entropic functional. All logarithms are natural; only the reference density must be faithful.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, PDF p. 13, finite-ancilla-tomography

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

noncomputable section

open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

/-- Finite ancilla state tomography: arXiv:2409.15485v2, PDF pp.13--14,
Equation (2.16). The initial system density nu need not be faithful. -/
theorem finiteAncillaTomography {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (H omega nu : Matrix I I ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ)
    (hH : H.IsHermitian) (homega : QAlgorithms.IsDensityMatrix omega)
    (hfaithful : omega.PosDef) (hnu : QAlgorithms.IsDensityMatrix nu)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hcoherence : rho 0 1 ≠ 0)
    (t : ℝ) (alpha : ℂ) (himaginary : alpha.re = 0) :
    QAlgorithms.traceLeft
      (finiteDensityAt (finiteAncillaHamiltonian H omega alpha)
        (Matrix.kronecker nu rho) t) =
      ancillaReadout rho (finiteAncillaFunctional H omega nu t alpha) := by sorry

end QAlgorithms.Papers.Independent.Next46.P01

end
