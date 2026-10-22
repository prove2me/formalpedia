-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_adComposition
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.adComposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:41:45.655386+00:00
-- url     : https://prove2.me/theorems/9ce381e9-017f-4e38-837b-28ea2f884dee
-- title:
--   Amplitude-damping channel concatenation
-- statement:
--   For survival probabilities $\eta,\eta'\in[0,1]$, let $D_\eta$ be the physical qubit amplitude-damping channel with Kraus operators $\operatorname{diag}(1,\sqrt\eta)$ and $\sqrt{1-\eta}|0\rangle\langle1|$. Then, as maps on all qubit operators,
--
--   $$D_\eta\circ D_{\eta'}=D_{\eta\eta'}.$$
--
--   Map equality also fixes the linear extension to a subsystem of an entangled input. It is the concatenation relation used for the degradation thresholds.
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

/-- PDF p.3: concatenation equality is on all operators, including its linear
extension to inputs entangled with an arbitrary retained reference. -/
theorem adComposition (eta eta2 : ℝ) (h1 : eta ∈ Set.Icc (0 : ℝ) 1)
    (h2 : eta2 ∈ Set.Icc (0 : ℝ) 1) :
    adChannel eta ∘ adChannel eta2 = adChannel (eta*eta2) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
