-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_entropy_production_nonadditivity
-- name    : QAlgorithms.Papers.Independent.Gap20.P06.entropy_production_nonadditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:21:45.274977+00:00
-- url     : https://prove2.me/theorems/bee9c4ba-131d-4245-ac92-8687ca433b0a
-- title:
--   Overall entropy production can be smaller than both stage values
-- statement:
--   There exist positive finite dimensions $q,r,s$, a density operator $\rho$ on $Q=\mathbb C^q$, a unit purification $|\Psi\rangle\in\mathbb C^r\otimes Q$ of $\rho$, two CPTP maps $\Phi,\Gamma:Q\to Q$, and a unit purification $|\chi\rangle\in\mathbb C^s\otimes Q$ of the intermediate state $\Phi(\rho)$ such that, in bits,
--
--   $$
--   S_e(\rho,\Gamma\circ\Phi)<S_e(\rho,\Phi),\qquad
--   S_e(\rho,\Gamma\circ\Phi)<S_e(\Phi(\rho),\Gamma).
--   $$
--
--   Here entropy production is the entropy of the actual reference-output density: the first and composite terms use $\Psi$, while the second-stage term uses $\chi$. The simultaneous inequalities exhibit failure of stagewise additivity and even monotonicity of entropy production.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, PDF p. 13, §5, observation before Eq.(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.13: overall entropy production may be strictly below both individual
values. Stage two uses a purification chi of the actual intermediate input.
No fixed lower bound on the existential system dimension is imposed. -/
theorem entropy_production_nonadditivity :
    ∃ (q r s : ℕ), 0 < q ∧ 0 < r ∧ 0 < s ∧
      ∃ (rho : Matrix (Fin q) (Fin q) ℂ)
        (psi : EuclideanSpace ℂ (Fin r × Fin q))
        (chi : EuclideanSpace ℂ (Fin s × Fin q))
        (f g : Superop (Fin q) (Fin q)),
        IsDensityMatrix rho ∧ ‖psi‖ = 1 ∧ traceLeft (pureDensity psi) = rho ∧
        IsChannel f ∧ IsChannel g ∧ ‖chi‖ = 1 ∧
        traceLeft (pureDensity chi) = f rho ∧
        vnEntropy (idTensorSuperop (g ∘ f) (pureDensity psi)) < vnEntropy (idTensorSuperop f (pureDensity psi)) ∧
        vnEntropy (idTensorSuperop (g ∘ f) (pureDensity psi)) < vnEntropy (idTensorSuperop g (pureDensity chi)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P06

end
