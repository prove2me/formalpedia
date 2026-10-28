-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_processedFano
-- name    : QAlgorithms.Papers.Independent.Support50.P41.processedFano
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:31:32.359782+00:00
-- url     : https://prove2.me/theorems/fa3969d4-e9c5-4aa9-8865-957c2a658afc
-- title:
--   §6.2, equations (26)–(28): optimized entanglement fidelity
-- statement:
--   For a density matrix $\rho$, CPTP map $\Phi$ on dimension $d\ge1$, and normalized purification $\psi$, the maximum $\widehat F_e=\max_U F_e(\psi,\operatorname{Ad}_U\circ\Phi)$ over system unitaries is attained. Its value is independent of the purification, and
--
--   $$\widehat F_e\ge F_e,\qquad S_e(\rho,\Phi)\le h(\widehat F_e)+(1-\widehat F_e)\log_2(d^2-1),\qquad
--   S_e(\rho,\Phi)\le1+2(1-\widehat F_e)\log_2d.$$
--
--   The logarithmic bound is for $d\ge2$; at $d=1$, $\widehat F_e=1$ and $S_e=0$. These bounds retain the original channel's entropy because the processing is unitary.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 28, §6.2, equations (26)–(28): optimized entanglement fidelity

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

/-- PDF pp.27--28, (26)--(28): attained unitary-processing maximum and Fano with original entropy. -/
theorem processedFano {d a : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      let f := purificationFidelity psi (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) ∘ Phi)
      (∀ V : Matrix.unitaryGroup (Fin d) ℂ,
        purificationFidelity psi (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) ∘ Phi) ≤ f) ∧
      purificationFidelity psi Phi ≤ f ∧
      (∀ b (phi : EuclideanSpace ℂ (Fin b × Fin d)), IsPurification rho phi →
        ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
          purificationFidelity phi (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) ∘ Phi) =
          purificationFidelity psi (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) ∘ Phi)) ∧
      (d = 1 → f = 1 ∧ entropyExchange Phi rho = 0) ∧
      (2 ≤ d → entropyExchange Phi rho ≤ binEntropy2 f + (1-f)*Real.logb 2 ((d : ℝ)^2-1)) ∧
      entropyExchange Phi rho ≤ 1+2*(1-f)*Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
