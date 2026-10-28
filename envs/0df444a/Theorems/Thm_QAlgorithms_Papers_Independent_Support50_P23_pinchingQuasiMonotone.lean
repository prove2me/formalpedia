-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_pinchingQuasiMonotone
-- name    : QAlgorithms.Papers.Independent.Support50.P23.pinchingQuasiMonotone
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-24T19:27:41.783921+00:00
-- url     : https://prove2.me/theorems/f6bdc22a-c1b6-4c3a-b01a-d16f07fbcb39
-- title:
--   Petz quasi-entropy is monotone under pinching ($1<\alpha\le 2$)
-- statement:
--   Let $\rho$ and $N$ be positive semidefinite matrices on a finite-dimensional space with $\mathrm{supp}\,\rho\subseteq\mathrm{supp}\,N$ (i.e. $\ker N\subseteq\ker\rho$). Let $\{|\psi_i\rangle\}$ be an orthonormal basis (the columns of a unitary $U$). Put $r_i=\langle\psi_i|\rho|\psi_i\rangle$ and $s_i=\langle\psi_i|N|\psi_i\rangle$. Then for $1<\alpha\le 2$,
--   $$\sum_i r_i^{\alpha}\,s_i^{1-\alpha}\;\le\;\mathrm{tr}\big(\rho^{\alpha}N^{1-\alpha}\big),$$
--   where $N^{1-\alpha}$ is taken on the support of $N$ (zero eigenvalues stay zero), and terms with $s_i=0$ (which force $r_i=0$) are $0$.
--
--   This is the data-processing inequality for the Petz quasi-entropy $S_{g_\alpha}(A,B)=\mathrm{tr}(A^\alpha B^{1-\alpha})$, $g_\alpha(t)=t^\alpha$ operator convex for $\alpha\in(1,2]$ (Lemma 14 of the source), applied to the pinching channel $X\mapsto\sum_i|\psi_i\rangle\langle\psi_i|X|\psi_i\rangle\langle\psi_i|$. It is exactly the step used in the proof of Theorem 7 (between (23) and the conclusion), with $\{\psi_i\}$ the eigenbasis of $\rho_{AB}-\lambda\,\mathbb 1_A\otimes\sigma_B$.
-- source:
--   Tomamichel, Colbeck, Renner, A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, proof of Theorem 7 (PDF pp.4-5) using Lemma 14 (Appendix A, Petz monotonicity) with the pinching TP-CPM

import Mathlib

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

/-- Proof of Theorem 7, PDF pp.4-5: Lemma 14 (Petz monotonicity of the quasi-entropy
S_{g_alpha}, g_alpha(t)=t^alpha operator convex for 1<alpha<=2) applied to the pinching
TP-CPM in the orthonormal basis given by the columns of U. Zero eigenvalues of N are
dropped in N^{1-alpha} (support convention); supp rho ⊆ supp N. -/
theorem pinchingQuasiMonotone {I : Type*} [Fintype I] [DecidableEq I]
    (rho N : Matrix I I ℂ) (hrho : rho.PosSemidef) (hN : N.PosSemidef)
    (hsupp : LinearMap.ker N.mulVecLin ≤ LinearMap.ker rho.mulVecLin)
    (U : Matrix.unitaryGroup I ℂ) (alpha : ℝ) (halpha : 1 < alpha) (halpha2 : alpha ≤ 2) :
    ∑ i, (((U : Matrix I I ℂ)ᴴ * rho * U) i i).re ^ alpha *
        (((U : Matrix I I ℂ)ᴴ * N * U) i i).re ^ (1 - alpha) ≤
      (cfc (fun x : ℝ => x ^ alpha) rho *
        cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - alpha)) N).trace.re := by sorry

end QAlgorithms.Papers.Independent.Support50.P23
