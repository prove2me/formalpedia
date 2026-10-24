-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_optimumRecoverySDP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.optimumRecoverySDP
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:16:46.724169+00:00
-- url     : https://prove2.me/theorems/d6cd5c19-de28-4d9a-bc98-d70fcc48e83d
-- title:
--   Optimum recovery is an attained semidefinite program
-- statement:
--   Let $H=\mathbb C^h$ and $K=\mathbb C^k$, with $h,k>0$, and fix a density operator $\rho$ on $H$ and a CPTP noise channel $\mathcal E:L(H)\to L(K)$ with finite Kraus operators $E_j$. For any normalized purification $|\psi\rangle$ of $\rho$, define $F_e(\rho,\mathcal B)=\langle\psi|(I\otimes\mathcal B)(|\psi\rangle\langle\psi|)|\psi\rangle$. With output-first, unnormalized operator kets, put $C_{\rho,\mathcal E}=\sum_j|\rho E_j^\dagger\rangle\rangle\langle\langle\rho E_j^\dagger|$. Then
--
--   $$
--   \max_{\mathcal R\;\mathrm{CPTP}}F_e(\rho,\mathcal R\circ\mathcal E)
--   =\max_{X\succeq0,\;\operatorname{tr}_H X=I_K}\operatorname{tr}(XC_{\rho,\mathcal E}).
--   $$
--
--   Both maxima are attained. Every recovery gives a feasible $X=X_{\mathcal R}$ with this objective, and every feasible $X$ is the Choi matrix of a CPTP recovery. This identifies the exact recovery problem with an SDP; it supplies no bit-complexity claim.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 4, Abstract; IV, Eq. (22): optimum entanglement-fidelity recovery is an attained SDP

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF pp.1–4, abstract and (7), (22): the exact recovery SDP has an attained maximum.
Every feasible Choi matrix is included, and every CPTP recovery is compared. -/
theorem optimumRecoverySDP {h k a m : ℕ} (hh : 0 < h) (hk : 0 < k)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) (hE : IsKrausFamily E) :
    (∀ R : Superop (Fin k) (Fin h), IsChannel R →
      ChoiFeasible (outputFirstChoi R) ∧ purificationFidelity psi (R ∘ krausApply E) =
        (outputFirstChoi R * recoveryCoefficient rho E).trace.re) ∧
    (∀ X : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ, ChoiFeasible X →
      ∃ R : Superop (Fin k) (Fin h), IsChannel R ∧ outputFirstChoi R = X) ∧
    ∃ (R : Superop (Fin k) (Fin h))
      (X : Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ),
      IsChannel R ∧ outputFirstChoi R = X ∧ ChoiFeasible X ∧
      purificationFidelity psi (R ∘ krausApply E) =
        (X * recoveryCoefficient rho E).trace.re ∧
      (∀ Y, ChoiFeasible Y → (Y * recoveryCoefficient rho E).trace.re ≤
        (X * recoveryCoefficient rho E).trace.re) ∧
      (∀ S : Superop (Fin k) (Fin h), IsChannel S →
        purificationFidelity psi (S ∘ krausApply E) ≤
          purificationFidelity psi (R ∘ krausApply E)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
