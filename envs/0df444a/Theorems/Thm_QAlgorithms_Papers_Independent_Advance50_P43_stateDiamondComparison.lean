-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P43_stateDiamondComparison
-- name    : QAlgorithms.Papers.Independent.Advance50.P43.stateDiamondComparison
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:15:37.16065+00:00
-- url     : https://prove2.me/theorems/14ab306d-6563-4dc8-970c-76b3ad9d11c7
-- title:
--   Generic state-induced and diamond distance comparison
-- statement:
--   Let $Q,B$ be nonzero finite-dimensional registers, $M_Q=\dim Q$, and let $\Phi,\Psi$ be CPTP maps from $Q$ to $B$. Define $d_1(\Phi,\Psi)=\sup_{\rho_Q\text{ density}}\|\Phi(\rho_Q)-\Psi(\rho_Q)\|_1$. Define the full diamond distance by maximizing the output trace norm over normalized pure inputs on $Q'Q$, with an untouched reference $Q'\cong Q$. Then
--
--   $$d_1(\Phi,\Psi)\le\|\Phi-\Psi\|_\diamond\le2M_Qd_1(\Phi,\Psi).$$
--
--   The estimate compares state discrimination without and with an untouched reference. Both distances use the full trace norm, without a factor of one half.
-- source:
--   Quantum-capacity bounds in spin-network communication channels, arXiv:1905.11920v2, PDF p. 6, §III.B / Appendix A, Eq.(44)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45
  (holevoCapacity resourceCapacity standardEbit)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer diamond)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst privateCapacity)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumCapacity)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

variable {A B C Q : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype Q]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q]

/-- arXiv:1905.11920v2, PDF p.6, (44), Appendix A p.8: generic channel norm
comparison, with MQ (the input dimension) in both Schmidt count and final factor.
The Appendix's printed MA labels are inconsistent with (44). -/
theorem stateDiamondComparison [Nonempty Q] [Nonempty B]
    (Phi Psi : Superop Q B)
    (hPhi : IsChannel Phi) (hPsi : IsChannel Psi) :
    stateDistance Phi Psi ≤ diamond (Phi - Psi) ∧
      diamond (Phi - Psi) ≤ 2 * (Fintype.card Q : ℝ) * stateDistance Phi Psi := by sorry

end QAlgorithms.Papers.Independent.Advance50.P43

end
