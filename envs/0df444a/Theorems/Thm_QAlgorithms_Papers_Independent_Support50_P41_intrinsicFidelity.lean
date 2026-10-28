-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_intrinsicFidelity
-- name    : QAlgorithms.Papers.Independent.Support50.P41.intrinsicFidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:14:15.759754+00:00
-- url     : https://prove2.me/theorems/c6fa5e3e-51b1-4ec8-b13a-eb8eb93e9bba
-- title:
--   §4.1: purification independence of entanglement fidelity
-- statement:
--   Fix a finite-dimensional CPTP map $\Phi$ and density matrix $\rho$. Any normalized purifications $\psi$ and $\phi$ of $\rho$, on possibly different finite reference spaces, give
--
--   $$F_e(\psi,\Phi)=F_e(\phi,\Phi).$$
--
--   Moreover the output corresponding to $(U_R\otimes I_Q)\psi$ is $(U_R\otimes I_Q)\rho'_{RQ}(U_R^\dagger\otimes I_Q)$ for every reference unitary $U_R$, where $\rho'_{RQ}=(\mathrm{id}_R\otimes\Phi)(|\psi\rangle\langle\psi|)$. Thus fidelity is intrinsic to $\rho$ and $\Phi$.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 14, §4.1: purification independence of entanglement fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- PDF pp.13--14, (9): purification independence across reference dimensions, with unitary covariance. -/
theorem intrinsicFidelity {d a b : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (phi : EuclideanSpace ℂ (Fin b × Fin d)) (hphi : IsPurification rho phi) :
    purificationFidelity psi Phi = purificationFidelity phi Phi ∧
    ∀ U : Matrix.unitaryGroup (Fin a) ℂ,
      idTensorSuperop Phi (pureDensity
        (act (Matrix.kronecker (U : Matrix (Fin a) (Fin a) ℂ)
          (1 : Matrix (Fin d) (Fin d) ℂ)) psi)) =
      conjSuperop (Matrix.kronecker (U : Matrix (Fin a) (Fin a) ℂ)
        (1 : Matrix (Fin d) (Fin d) ℂ)) (idTensorSuperop Phi (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
