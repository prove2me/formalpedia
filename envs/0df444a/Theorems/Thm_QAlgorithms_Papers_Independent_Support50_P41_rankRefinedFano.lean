-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_rankRefinedFano
-- name    : QAlgorithms.Papers.Independent.Support50.P41.rankRefinedFano
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:30:31.956403+00:00
-- url     : https://prove2.me/theorems/0d3ca4d8-10b1-4bf0-b3b2-9a379b820db2
-- title:
--   §6.2: Fano bound using the support dimension of R
-- statement:
--   For a density matrix $\rho$, CPTP map $\Phi$ on dimension $d\ge1$, and any normalized finite-reference purification $\psi$, let $r=\operatorname{rank}(\operatorname{Tr}_Q|\psi\rangle\langle\psi|)$. Then $1\le r\le d$ and, for $rd>1$,
--
--   $$S_e(\rho,\Phi)\le h(F_e)+(1-F_e)\log_2(rd-1).$$
--
--   Here $F_e=F_e(\psi,\Phi)$; for $rd=1$ the values are $F_e=1$, $S_e=0$. Thus only the occupied reference support contributes, even when the reference itself is larger.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 27, §6.2: Fano bound using the support dimension of R

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

/-- PDF p.27: the occupied reference support replaces its ambient dimension in Fano. -/
theorem rankRefinedFano {d a : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi) :
    let r := (traceRight (pureDensity psi)).rank
    0 < r ∧ r ≤ d ∧
    (r*d = 1 → purificationFidelity psi Phi = 1 ∧ entropyExchange Phi rho = 0) ∧
    (1 < r*d → entropyExchange Phi rho ≤ binEntropy2 (purificationFidelity psi Phi) +
      (1-purificationFidelity psi Phi)*Real.logb 2 (((r*d : ℕ) : ℝ)-1)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
