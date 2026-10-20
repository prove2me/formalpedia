-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_codeRecoveryReduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.codeRecoveryReduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:23:08.959699+00:00
-- url     : https://prove2.me/theorems/421d0575-e151-40df-8ae8-c972a57dabcd
-- title:
--   Code-output recovery reduction and ambient Hermitian dimension
-- statement:
--   Let $H=\mathbb C^h$, $K=\mathbb C^k$, $0<h\le k$, and $U:H\to K$ be an isometry. Set $P_C=UU^\dagger$, and let $\rho$ be a density on $K$ satisfying $\rho=P_C\rho P_C$. Fix a CPTP noise $\mathcal E:K\to K$. Write $\mathrm{Enc}(M)=UMU^\dagger$ and $\mathrm{Dec}(M)=U^\dagger MU$. The maps
--
--   $$
--   \mathcal R\longmapsto\mathrm{Dec}\circ\mathcal R,\qquad
--   \mathcal S\longmapsto\mathrm{Enc}\circ\mathcal S
--   $$
--
--   are mutually inverse between CPTP recoveries $\mathcal R:K\to K$ satisfying $P_C\mathcal R(M)P_C=\mathcal R(M)$ for every matrix $M$, and all CPTP channels $\mathcal S:K\to H$. If $|\psi\rangle$ purifies $\rho'=U^\dagger\rho U$, then $(I\otimes U)|\psi\rangle$ purifies $\rho$, and
--
--   $$
--   F_e(\rho,\mathcal R\circ\mathcal E)
--   =F_e(\rho',\mathrm{Dec}\circ\mathcal R\circ\mathcal E\circ\mathrm{Enc}).
--   $$
--
--   The real dimensions of the ambient Hermitian matrix spaces for the two recovery Choi matrices are $k^4$ and $h^2k^2$, respectively, with ratio $(k/h)^2$. These counts precede partial-trace constraints. This gives the Figure 1 optimization reduction within code-output recoveries; $\mathrm{Dec}$ is not asserted to be TP on unrestricted ambient inputs.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 4, V and Fig. 1: code-supported recovery reduction and ambient SDP size

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF pp.4–5, Fig.1 and §V: code-output recoveries correspond exactly to logical-output
channels, preserving the purification objective. The count is real ambient Hermitian
dimension before affine constraints. The p.4 prose prints K tensor H for X_R; changed
to H tensor K because (21), (22) and recovery K → H determine that order. -/
theorem codeRecoveryReduction {h k a : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k)
    (U : Matrix (Fin k) (Fin h) ℂ) (hU : Uᴴ * U = 1)
    (rho : Matrix (Fin k) (Fin k) ℂ) (hrho : IsDensityMatrix rho)
    (hsupp : rho = codeProjector U * rho * codeProjector U)
    (psi : EuclideanSpace ℂ (Fin a × Fin h))
    (hpsi : IsPurification (Uᴴ * rho * U) psi)
    (E : Superop (Fin k) (Fin k)) (hE : IsChannel E) :
    IsPurification rho (encodedPurification U psi) ∧
    (∀ R : Superop (Fin k) (Fin k), IsChannel R → HasCodeOutputs U R →
      IsChannel (conjSuperop Uᴴ ∘ R) ∧
      conjSuperop U ∘ (conjSuperop Uᴴ ∘ R) = R) ∧
    (∀ S : Superop (Fin k) (Fin h), IsChannel S →
      IsChannel (conjSuperop U ∘ S) ∧ HasCodeOutputs U (conjSuperop U ∘ S) ∧
      conjSuperop Uᴴ ∘ (conjSuperop U ∘ S) = S) ∧
    (∀ R : Superop (Fin k) (Fin k), IsChannel R → HasCodeOutputs U R →
      purificationFidelity (encodedPurification U psi) (R ∘ E) =
        purificationFidelity psi ((conjSuperop Uᴴ ∘ R) ∘ E ∘ conjSuperop U)) ∧
    Module.finrank ℝ (selfAdjoint (Matrix (Fin k × Fin k) (Fin k × Fin k) ℂ)) = k ^ 4 ∧
    Module.finrank ℝ (selfAdjoint (Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ)) = h ^ 2 * k ^ 2 ∧
    (k : ℝ) ^ 4 / ((h : ℝ) ^ 2 * (k : ℝ) ^ 2) = ((k : ℝ) / (h : ℝ)) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
