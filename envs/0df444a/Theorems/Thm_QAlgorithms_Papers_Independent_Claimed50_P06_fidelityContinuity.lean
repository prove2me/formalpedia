-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P06_fidelityContinuity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P06.fidelityContinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:07:34.242132+00:00
-- url     : https://prove2.me/theorems/0d553a28-7fd2-4388-8c3c-0ead16c11f00
-- title:
--   Continuity of fidelity for unit vectors
-- statement:
--   Let $\mathcal A$ be a von Neumann algebra in standard form on a complex Hilbert space $\mathcal H$, and let $\psi_1,\psi_2,\phi_1,\phi_2\in\mathcal H$ all have norm one. Write $\omega_v(a)=\langle v,av\rangle$ and let $F$ denote unsquared fidelity. Then
--
--   $$\bigl|F(\omega_{\psi_1},\omega_{\phi_1})-F(\omega_{\psi_2},\omega_{\phi_2})\bigr|
--   \le\|\phi_1-\phi_2\|+\|\psi_1-\psi_2\|.$$
--
--   Thus fidelity varies continuously with normalized vector representatives.
--
--   **Formalization Note** Equation (218) identifies these fidelities with the Araki–Masuda quantities at $p=1$ for the commutant. The printed lemma omits normalization; the proof explicitly requires normalized vectors on PDF p.38. The formal statement records that source-backed correction.
-- source:
--   Approximate recovery and relative entropy I. general von Neumann subalgebras, arXiv:2006.08002v1, PDF p. 37, Lemma 11: continuity of fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Claimed50.P06

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 11, PDF pp.37–38, Eq.(219), expressed as fidelity using Eq.(218).
Printed: arbitrary vectors. Changed: all four vectors have norm one. Why: the
proof explicitly imposes this on p.38, and the unnormalized printed bound is
false already on H = C. This correction requires independent moderation. -/
theorem fidelityContinuity
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (_form : StandardForm A)
    (psi1 psi2 phi1 phi2 : H)
    (hPsi1 : ‖psi1‖ = 1) (hPsi2 : ‖psi2‖ = 1)
    (hPhi1 : ‖phi1‖ = 1) (hPhi2 : ‖phi2‖ = 1) :
    |vectorFidelity A psi1 phi1 - vectorFidelity A psi2 phi2| ≤
      ‖phi1 - phi2‖ + ‖psi1 - psi2‖ := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P06

end
