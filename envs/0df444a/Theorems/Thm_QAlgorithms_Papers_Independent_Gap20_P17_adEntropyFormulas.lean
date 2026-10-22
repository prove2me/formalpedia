-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_adEntropyFormulas
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.adEntropyFormulas
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:40:47.293106+00:00
-- url     : https://prove2.me/theorems/07058dac-c021-410c-9f99-ec20bae8c6eb
-- title:
--   Amplitude-damping entropy formulas
-- statement:
--   Let $0\le\eta,p\le1$. The amplitude-damping channel $D_\eta$ has no-emission Kraus operator $\operatorname{diag}(1,\sqrt\eta)$ and emission Kraus operator $\sqrt{1-\eta}|0\rangle\langle1|$. Thus $\eta$ is survival probability and $\rho_p=\operatorname{diag}(1-p,p)$ has excited population $p$. With entropies in bits,
--
--   $$D_\eta(\rho_p)=\operatorname{diag}(1-\eta p,\eta p),\quad I(D_\eta,\rho_p)=H_2(\eta p)-H_2((1-\eta)p),\quad I_R(D_\eta,\rho_p)=H_2(p)-H_2((1-\eta)p).$$
--
--   These formulas include pure input and channel endpoints and supply the one-variable information objectives.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 3, Eq.(9)

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

/-- PDF p.3, Eq.(9): survival eta, excited population p, including both endpoints.
The E argument printed in (9) denotes D_eta from the surrounding paragraph. -/
theorem adEntropyFormulas (eta p : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    adChannel eta (diagonalInput p) = diagonalInput (eta*p) ∧
    forwardInfo (adDilation eta) (diagonalInput p) =
      binEntropy2 (eta*p) - binEntropy2 ((1-eta)*p) ∧
    reverseInfo (adDilation eta) (diagonalInput p) =
      binEntropy2 p - binEntropy2 ((1-eta)*p) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
