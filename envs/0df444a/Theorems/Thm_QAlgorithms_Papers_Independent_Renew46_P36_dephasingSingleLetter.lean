-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_dephasingSingleLetter
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.dephasingSingleLetter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:13:38.684842+00:00
-- url     : https://prove2.me/theorems/3019683f-e9b3-448c-9af4-9b8766f9f479
-- title:
--   Appendix B: single-letter entire simultaneous region
-- statement:
--   Let $\mathcal N$ be a generalized dephasing channel on a finite nonzero register, specified by $U|i\rangle=|i\rangle|\phi_i\rangle$ with normalized vectors in a finite nonzero environment. For any of the unassisted operational scenarios Ia, Ib, or II, let $S_s(\mathcal N)$ be the nonnegative asymptotic simultaneous capacity region with per-message correctness and squared quantum fidelity. Define $S^{(1)}(\mathcal N)$ using finite normalized pure input–reference ensembles, with both bounds supplied by the same ensemble:
--
--   $$
--   S_s(\mathcal N)=S^{(1)}(\mathcal N)
--   =\bigcup_{\{p_x,\phi_x^{AA'}\}}
--   \{(r,R)\geq0:r\leq I(X;B),\ R\leq I(A\rangle BX)\}.
--   $$
--
--   The information quantities are in bits and use the channel outputs $(\mathrm{id}\otimes\mathcal N)(\phi_x)$. Thus the entire simultaneous region single-letterizes for generalized dephasing channels. This statement does not extend the conclusion to all degradable channels.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 14, Appendix B: single-letter entire simultaneous region

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Appendix B, PDF pp.13--14 (announced p.5): the ENTIRE simultaneous region
single-letterizes for generalized dephasing channels, not for arbitrary degradable
channels. The printed reference to lemma 6 means Lemma 7. -/
theorem dephasingSingleLetter
    [Nonempty A] [Nonempty E] (env : A → EuclideanSpace ℂ E)
    (henv : ∀ a, ‖env a‖ = 1) (s : Scenario) :
    simultaneousOperationalRegion s (generalizedDephasing env) = cqOneLetterRegion (generalizedDephasing env) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
