-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_codeIsometryNoise
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.codeIsometryNoise
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:22:20.939948+00:00
-- url     : https://prove2.me/theorems/da794d94-eddd-4f32-8392-dc2729c40377
-- title:
--   Code isometry can be incorporated into the noise
-- statement:
--   Let $H=\mathbb C^h$, $K=\mathbb C^k$, $0<h\le k$, and let $U:H\to K$ satisfy $U^\dagger U=I_H$. Its orthonormal columns are the logical codewords $|n\rangle_L$, and $P_C=UU^\dagger=\sum_n|n\rangle_L\langle n|_L$. Let $\rho$ be a density operator on $K$ with $\rho=P_C\rho P_C$. For CPTP noise on $K$ with Kraus family $E_j$, set $\rho'=U^\dagger\rho U$ and $E_j'=E_jU$. Then $\rho'$ is a density, $\sum_j(E_j')^\dagger E_j'=I_H$, and
--
--   $$
--   \mathcal E'(\rho')=\sum_jE_j'\rho'(E_j')^\dagger=\mathcal E(\rho).
--   $$
--
--   This is equality of full output operators. It reduces the logical input space without changing the noisy state.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 5, V, Eqs. (24)-(25): incorporating a code isometry into the noise

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF pp.4–5, (24)–(25): incorporating an isometric code into the noise preserves outputs. -/
theorem codeIsometryNoise {h k m : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k)
    (U : Matrix (Fin k) (Fin h) ℂ) (hU : Uᴴ * U = 1)
    (rho : Matrix (Fin k) (Fin k) ℂ) (hrho : IsDensityMatrix rho)
    (hsupp : rho = codeProjector U * rho * codeProjector U)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ) (hE : IsKrausFamily E) :
    codeProjector U = ∑ i, dyad (WithLp.toLp 2 (fun x => U x i))
      (WithLp.toLp 2 (fun x => U x i)) ∧
    IsDensityMatrix (Uᴴ * rho * U) ∧
    IsKrausFamily (fun j => E j * U) ∧
    krausApply (fun j => E j * U) (Uᴴ * rho * U) = krausApply E rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
