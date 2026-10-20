-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_choiChannelCorrespondence
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.choiChannelCorrespondence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:19:39.578626+00:00
-- url     : https://prove2.me/theorems/017bc7b8-ed6c-4f4d-a026-5099ba12c6ff
-- title:
--   Choi reconstruction and exact channel characterization
-- statement:
--   Let $H=\mathbb C^h$ and $K=\mathbb C^k$, $h,k>0$. For a finite family $E_j:H\to K$, set $\mathcal E(M)=\sum_jE_jME_j^\dagger$ and $X_E=\sum_j|E_j\rangle\rangle\langle\langle E_j|$. Then
--
--   $$
--   \mathcal E(M)=\operatorname{tr}_H[(I_K\otimes M^T)X_E],\qquad
--   \sum_j E_j^\dagger E_j=I_H\iff\operatorname{tr}_K X_E=I_H.
--   $$
--
--   The second condition is also equivalent to $\operatorname{tr}\mathcal E(\sigma)=1$ for every input density operator $\sigma$. Every positive semidefinite $X$ has a finite operator-ket Gram decomposition. If $\Phi_X(M)=\operatorname{tr}_H[(I_K\otimes M^T)X]$, then
--
--   $$
--   X\succeq0\ \text{and}\ \operatorname{tr}_KX=I_H\iff\Phi_X\ \text{is CPTP}.
--   $$
--
--   The intrinsic Choi matrix $X_\Phi=\sum_{i,j}\Phi(|i\rangle\langle j|)\otimes|i\rangle\langle j|$ satisfies $X_{\Phi_X}=X$ for every $X$, $X_\mathcal E=X_E$, and $\Phi_{X_\Phi}=\Phi$ for every channel. These inverse constructions give the one-to-one correspondence used by the SDP, credited in the source to [14]–[16].
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 3, III, Eqs. (13)-(15): channel reconstruction and trace-preserving Choi constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.3, (13)–(15) and the one-to-one correspondence credited to [14]–[16].
Includes reconstruction on every matrix, positivity's Kraus converse, both channel
correspondence directions, and the all-density trace-one test. -/
theorem choiChannelCorrespondence {h k m : ℕ} (hh : 0 < h) (hk : 0 < k)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) :
    (∀ M, krausApply E M = fromOutputFirstChoi (krausChoi E) M) ∧
    outputFirstChoi (krausApply E) = krausChoi E ∧
    (IsKrausFamily E ↔ traceLeft (krausChoi E) = 1) ∧
    ((∀ rho, IsDensityMatrix rho → (krausApply E rho).trace = 1) ↔
      traceLeft (krausChoi E) = 1) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ,
      X.PosSemidef ↔ ∃ (n : ℕ) (A : Fin n → Matrix (Fin k) (Fin h) ℂ), X = krausChoi A) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ,
      ChoiFeasible X ↔ IsChannel (fromOutputFirstChoi X)) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ, outputFirstChoi (fromOutputFirstChoi X) = X) ∧
    (∀ B : Superop (Fin h) (Fin k), IsChannel B → fromOutputFirstChoi (outputFirstChoi B) = B) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
