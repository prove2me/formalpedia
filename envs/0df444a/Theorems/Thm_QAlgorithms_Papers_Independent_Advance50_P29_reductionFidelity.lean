-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_reductionFidelity
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.reductionFidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:03:57.185715+00:00
-- url     : https://prove2.me/theorems/eb2569e4-c619-427e-a112-d87edf8ab589
-- title:
--   §1.2, (4): deleting Kraus operators cannot increase entanglement fidelity
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. Let $\mathcal E:B(Q)\to B(Q)$ have a minimal finite Kraus family satisfying $\sum_iA_i^\dagger A_i\le I$, and let $\widetilde{\mathcal E}$ retain any subset of that family. For every density operator $\rho$,
--
--   $$
--   F_e(\rho,\widetilde{\mathcal E})\le F_e(\rho,\mathcal E).
--   $$
--
--   This permits discarding selected Kraus terms in a lower-bound argument. No postselection normalization is used.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 4, §1.2, (4): deleting Kraus operators cannot increase entanglement fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF p.4, (4): deleting Kraus operators cannot increase entanglement fidelity.
The printed F is F_e, as the preceding sentence and (2) specify.
The supplied family is minimal, as the source indexes it by the channel length. -/
theorem reductionFidelity [Nonempty I] (A : L → Matrix I I ℂ)
    (hA : KrausTraceBound A) (hm : MinimalKraus A) (s : Finset L) (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) :
    stateEntanglementFidelity (krausApply (fun i : s => A i)) rho ≤
      stateEntanglementFidelity (krausApply A) rho := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
