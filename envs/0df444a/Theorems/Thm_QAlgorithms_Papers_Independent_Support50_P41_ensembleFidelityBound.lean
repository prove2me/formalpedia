-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_ensembleFidelityBound
-- name    : QAlgorithms.Papers.Independent.Support50.P41.ensembleFidelityBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:19:27.118556+00:00
-- url     : https://prove2.me/theorems/f9009acd-6024-465f-a705-36e5671818d7
-- title:
--   §4.3: average ensemble fidelity is bounded below by F_e
-- statement:
--   Let $p_k\ge0$ be a countable probability law, $v_k$ unit vectors, and $\rho=\sum_k p_k|v_k\rangle\langle v_k|$. Fix one CPTP map $\Phi$ and a normalized purification $\psi$ of $\rho$. The average squared fidelity converges and satisfies
--
--   $$F_e(\psi,\Phi)\le\overline F:=\sum_k p_k F(|v_k\rangle\langle v_k|,\Phi(|v_k\rangle\langle v_k|)).$$
--
--   No orthogonality of the component states is required. This extends entanglement preservation to every ensemble of the same density matrix.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 19, §4.3: average ensemble fidelity is bounded below by F_e

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

/-- PDF pp.17--19: any countable pure ensemble has average fidelity at least entanglement fidelity. -/
theorem ensembleFidelityBound {K : Type*} [Countable K] {d a : ℕ} [NeZero d]
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k) (htotal : HasSum p 1)
    (v : K → EuclideanSpace ℂ (Fin d)) (hv : ∀ k, IsState (v k))
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (havg : HasSum (fun k => (p k : ℂ) • pureDensity (v k)) rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi) :
    Summable (fun k => p k * rootFidelity (pureDensity (v k)) (Phi (pureDensity (v k)))^2) ∧
    purificationFidelity psi Phi ≤
      ∑' k, p k * rootFidelity (pureDensity (v k)) (Phi (pureDensity (v k)))^2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
