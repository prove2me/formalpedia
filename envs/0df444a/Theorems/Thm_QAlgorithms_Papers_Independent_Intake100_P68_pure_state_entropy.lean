-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_pure_state_entropy
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.pure_state_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:08:54.154955+00:00
-- url     : https://prove2.me/theorems/7b10b869-3380-4b00-827e-81e83c14e12e
-- title:
--   Proposition 4: pure-state entropy in ebits
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   Assume additionally $E(\Phi^+)=1$, where $\Phi^+$ denotes the projector of $(|00\rangle+|11\rangle)/\sqrt2$. For every unit vector $\psi$ in positive finite bipartite local dimensions,
--
--   $$E(|\psi\rangle\langle\psi|)=S(\operatorname{Tr}_A|\psi\rangle\langle\psi|).$$
--
--   Here $S$ is von Neumann entropy with logarithms to base two. Either pure-state marginal has this entropy. The equality fixes the measure on pure states in ebit units.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 2, Proposition 4: pure-state entropy in ebits

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.2, Proposition 4: entropy of either pure-state marginal in ebits.
The norm-one condition and Bell normalization (10) are both essential. -/
theorem pure_state_entropy
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E) (hunit : resourceSingleValue E phiPlusDensity = 1)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (psi : EuclideanSpace ℂ (Fin a × Fin b)) (hpsi : ‖psi‖ = 1) :
    resourceSingleValue E (pureDensity psi) = vnEntropy (traceLeft (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
