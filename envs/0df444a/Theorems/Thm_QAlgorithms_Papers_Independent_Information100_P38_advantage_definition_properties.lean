-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_advantage_definition_properties
-- name    : QAlgorithms.Papers.Independent.Information100.P38.advantage_definition_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:04:09.845764+00:00
-- url     : https://prove2.me/theorems/133965ca-e174-4a41-bd68-d9ed84d7e933
-- title:
--   Definition 1, Eqs.(18)–(20)
-- statement:
--   Let $d,n\ge1$, let $M$ be a finite POVM, and let $H$ be diagonal with weakly increasing real energies. For a density matrix $\rho$, put $\Phi_M(\rho)=\sum_{\mu:\operatorname{Tr}M_\mu\ne0}\operatorname{Tr}(M_\mu\rho)M_\mu/\operatorname{Tr}M_\mu$, and let $P_H$ denote minimum energy on the unitary orbit. Write $E_O(\rho,M)=\operatorname{Tr}(H\rho)-P_H(\Phi_M(\rho))$ and $E_{\rm inc}(\rho)=\operatorname{Tr}(H\Delta\rho)-P_H(\Delta\rho)$. Then
--
--   $$A_H^M=\max_\rho\{E_O(\rho,M)-E_{\rm inc}(\rho)\}=\max_\rho\{P_H(\Delta\rho)-P_H(\Phi_M(\rho))\}\ge0.$$
--
--   Both optimizations range over exactly the density matrices and the maximum is attained. For every input, $\max_N E_O(\rho,N)=E_{\rm inc}(\rho)$, attained by an incoherent POVM $N$, where the benchmark permits any positive finite number of outcomes. Thus replacing the incoherent ergotropy in the first maximum by this benchmark gives the same advantage. This supplies the state-independent operational definition.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 5, Definition 1, Eqs.(18)–(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper pp.4–5, Definition 1, Eqs.(18)–(20): nonnegativity, actual attainment,
all-outcome incoherent benchmark, and passive-energy reformulation. -/
theorem advantage_definition_properties {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    0 ≤ observationalAdvantage E M ∧
    (∃ X, IsDensityMatrix X ∧ observationalAdvantage E M =
      observationalErgotropy E M X - incoherentErgotropy E X) ∧
    observationalAdvantage E M = sSup {r | ∃ X, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentWorkBenchmark E X} ∧
    observationalAdvantage E M = sSup {r | ∃ X, IsDensityMatrix X ∧
      r = passiveEnergy E (energyDephasing X) - passiveEnergy E (ergotropicCoarseGraining M X)} ∧
    (∀ X, IsDensityMatrix X → incoherentWorkBenchmark E X = incoherentErgotropy E X ∧
      ∃ m : ℕ, 0 < m ∧ ∃ N : Fin m → Matrix (Fin d) (Fin d) ℂ,
        IsPOVM N ∧ measurementIncoherent N ∧
        observationalErgotropy E N X = incoherentWorkBenchmark E X) := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
