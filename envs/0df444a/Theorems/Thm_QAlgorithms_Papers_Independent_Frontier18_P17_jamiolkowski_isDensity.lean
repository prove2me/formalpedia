-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_jamiolkowski_isDensity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.jamiolkowski_isDensity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:31:03.534978+00:00
-- url     : https://prove2.me/theorems/adce2d2b-c565-469b-8487-ee829fcdd9cd
-- title:
--   Normalized dynamical matrices are density matrices
-- statement:
--   Let $N\ge1$ and let $\Phi:M_N(\mathbb C)\to M_N(\mathbb C)$ be complex-linear, completely positive and trace preserving. Define its output-first dynamical matrix by $D_{(a,i),(b,j)}=\Phi(E_{ij})_{ab}$, where $E_{ij}$ are canonical matrix units, and set $\rho_\Phi=D/N$. Then
--
--   $$D\succeq0,\qquad\operatorname{tr}D=N,\qquad\rho_\Phi\succeq0,\qquad\operatorname{tr}\rho_\Phi=1.$$
--
--   Thus the normalized dynamical matrix is a bipartite density matrix. This is the forward density property of the correspondence, without a surjectivity claim onto all bipartite states.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 6, §IV A, Eq.(43)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.6, Eq. (43) and precursor: dynamical trace N, and a normalized density
matrix. No claim of surjectivity onto all bipartite density matrices is made. -/
theorem jamiolkowski_isDensity {N : ℕ} (hN : 0 < N)
    (Phi : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (hPhi : CPTP Phi) :
    (dynamical Phi).PosSemidef ∧ (dynamical Phi).trace = (N : ℂ) ∧
      QAlgorithms.IsDensityMatrix (jamiolkowski Phi) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
