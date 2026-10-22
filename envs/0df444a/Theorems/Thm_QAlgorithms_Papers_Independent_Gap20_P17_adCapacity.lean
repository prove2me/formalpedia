-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_adCapacity
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.adCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:43:20.362608+00:00
-- url     : https://prove2.me/theorems/0195f426-15ba-427f-b199-fcab93dc051a
-- title:
--   Amplitude-damping unassisted capacity
-- statement:
--   Operational capacities are supremal asymptotic ebits per physical channel use, with vanishing full-state trace-norm error, arbitrary finite block memories, and no initial shared entanglement. $E$ allows local processing without classical assistance; $E_{\leftarrow}$ permits adaptive feedback; $E_{\leftrightarrow}$ permits both classical directions. $E_{\triangleleft}$ sends the entire block before one final Bob-to-Alice message and Alice's conditional operation. Rate zero is included. For the qubit amplitude-damping channel with survival $\eta\in[0,1]$, the unassisted capacity equals its optimized one-use coherent information:
--
--   $$E(D_\eta)=\max_\rho I(D_\eta,\rho)=\begin{cases}0,&\eta\le\tfrac12,\\
--   \displaystyle\max_{0\le p\le1}\big[H_2(\eta p)-H_2((1-\eta)p)\big],&\eta>\tfrac12.
--   \end{cases}$$
--
--   The positive-regime optimization uses diagonal inputs with excited population $p$. Pure inputs attain zero in the other regime; no fixed-population dephasing claim is made there.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 5, p.3 threshold paragraph and p.5 appendix

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

/-- PDF pp.3,5: unassisted AD capacity, including the antidegradable zero branch;
this does not assert fixed-population dephasing optimality below eta=1/2. -/
theorem adCapacity (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    entanglementCapacity (adChannel eta) .unassisted = (forwardMaximum (adDilation eta) : EReal) ∧
    forwardMaximum (adDilation eta) =
      if eta ≤ 1/2 then 0 else
        populationMaximum (fun p => binEntropy2 (eta*p)-binEntropy2 ((1-eta)*p)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
