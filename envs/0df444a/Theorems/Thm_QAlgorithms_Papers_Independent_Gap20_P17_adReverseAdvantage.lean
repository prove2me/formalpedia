-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_adReverseAdvantage
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.adReverseAdvantage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:44:17.225621+00:00
-- url     : https://prove2.me/theorems/0510359d-0309-4f59-b222-fda31037d579
-- title:
--   Strict reverse-information advantage for nontrivial AD
-- statement:
--   Operational capacities are supremal asymptotic ebits per physical channel use, with vanishing full-state trace-norm error, arbitrary finite block memories, and no initial shared entanglement. $E$ allows local processing without classical assistance; $E_{\leftarrow}$ permits adaptive feedback; $E_{\leftrightarrow}$ permits both classical directions. $E_{\triangleleft}$ sends the entire block before one final Bob-to-Alice message and Alice's conditional operation. Rate zero is included.
--
--   Let $D_\eta$ be qubit amplitude damping with survival $\eta$, and let $R_1(D_\eta)=\max_\rho I_R(D_\eta,\rho)$ be the signed reverse-information maximum. The endpoint-corrected statement is
--
--   $$R_1(D_\eta)>E(D_\eta)\quad(0<\eta<1),\qquad R_1(D_\eta)>0=E(D_\eta)\quad(0<\eta\le\tfrac12),$$
--   $$R_1(D_0)=E(D_0)=0,\qquad R_1(D_1)=E(D_1)=1.$$
--
--   This is the strict reverse-information advantage supported by Eq.(9) and Fig.4, with the degenerate channels made explicit.
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

/-- PDF p.3, corrected endpoint reading of the prose and Fig.4: strict reverse
advantage holds for 0<eta<1, with equalities at eta=0 and eta=1. The printed
'all eta' and positivity at eta=0 are false; see HARD.md and the trap audit. -/
theorem adReverseAdvantage :
    (∀ eta : ℝ, 0 < eta → eta < 1 →
      entanglementCapacity (adChannel eta) .unassisted < (reverseMaximum (adDilation eta) : EReal)) ∧
    (∀ eta : ℝ, 0 < eta → eta ≤ 1/2 →
      0 < reverseMaximum (adDilation eta) ∧ entanglementCapacity (adChannel eta) .unassisted = 0) ∧
    reverseMaximum (adDilation 0) = 0 ∧ entanglementCapacity (adChannel 0) .unassisted = 0 ∧
    reverseMaximum (adDilation 1) = 1 ∧ entanglementCapacity (adChannel 1) .unassisted = 1 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
