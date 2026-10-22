-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_adDegradability
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.adDegradability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:42:28.948129+00:00
-- url     : https://prove2.me/theorems/388dce0a-27cb-4e7a-b5a5-cdaf5e57334d
-- title:
--   Amplitude-damping degradation thresholds
-- statement:
--   Let $\eta\in[0,1]$ be the survival probability of the physical qubit amplitude-damping channel $D_\eta$, with its two-dimensional pure dilation environment. Then
--
--   $$\eta\ge\tfrac12\ \Longrightarrow\ \exists\mathcal T\text{ CPTP}:\ D_\eta^c=\mathcal T\circ D_\eta,\qquad
--   \eta\le\tfrac12\ \Longrightarrow\ \exists\mathcal G\text{ CPTP}:\ D_\eta=\mathcal G\circ D_\eta^c.$$
--
--   The equalities hold on all operators, and the chosen dilation is isometric. Both properties apply at $\eta=1/2$. Capacity formulas are stated separately.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 3, paragraph below Fig.4

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3: physical degrading and antidegrading maps exist in the respective
survival regimes; at eta=1/2 both properties hold. -/
theorem adDegradability (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (1/2 ≤ eta → IsDegradable (adDilation eta)) ∧
    (eta ≤ 1/2 → IsAntidegradable (adDilation eta)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
