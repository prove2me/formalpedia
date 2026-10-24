-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_quantumFano
-- name    : QAlgorithms.Papers.Independent.Support50.P41.quantumFano
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:11:46.067729+00:00
-- url     : https://prove2.me/theorems/aec73939-bda3-4163-b9d4-82c54b3d319b
-- title:
--   §6.2, equations (24)–(25): quantum Fano inequality
-- statement:
--   Let $\Phi$ be a complex-linear completely positive trace-preserving map on a $d$-dimensional system, $d\ge1$, and let $\psi$ be any normalized purification of a density matrix $\rho$. Write $F_e=\langle\psi|(\mathrm{id}\otimes\Phi)(|\psi\rangle\langle\psi|)|\psi\rangle$ and $S_e$ for the entropy of this joint output. Entropies and $h$ are in bits. For $d\ge2$,
--
--   $$S_e\le h(F_e)+(1-F_e)\log_2(d^2-1),\qquad S_e\le1+2(1-F_e)\log_2d.$$
--
--   For $d=1$, $F_e=1$ and $S_e=0$. This relates entanglement preservation to entropy exchange.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 27, §6.2, equations (24)–(25): quantum Fano inequality

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

/-- PDF pp.26--27, (24)--(25): quantum Fano inequality; the singleton branch avoids log zero. -/
theorem quantumFano {d a : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi) :
    (d = 1 → purificationFidelity psi Phi = 1 ∧ entropyExchange Phi rho = 0) ∧
    (2 ≤ d → entropyExchange Phi rho ≤ binEntropy2 (purificationFidelity psi Phi) +
      (1 - purificationFidelity psi Phi) * Real.logb 2 ((d : ℝ)^2 - 1)) ∧
    entropyExchange Phi rho ≤ 1 + 2*(1-purificationFidelity psi Phi)*Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
