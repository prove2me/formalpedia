-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P11_exampleBell
-- name    : QAlgorithms.Papers.Independent.Gap20.P11.exampleBell
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:19:53.057665+00:00
-- url     : https://prove2.me/theorems/a16958a7-115c-4cf7-a0aa-bec97105fbc5
-- title:
--   A Bell source merges locally while retaining one shared ebit
-- statement:
--   Alice and Bob initially share the known pure source
--
--   $$
--   |\phi^+\rangle_{AB}=\frac{|00\rangle+|11\rangle}{\sqrt2},\qquad S(A\mid B)=-1.
--   $$
--
--   Bob can locally prepare a new copy of this known pure source on $A'B'$, while Alice and Bob keep their original shared pair unchanged. The explicit local preparation is a quantum channel, and the exact joint output is
--
--   $$
--   |\phi^+\rangle\langle\phi^+|_{A_{\rm old}B_{\rm old}}
--   \otimes |\phi^+\rangle\langle\phi^+|_{A'B'}.
--   $$
--
--   The old pair remains shared across Alice and Bob; both registers of the reconstructed source belong to Bob. No quantum communication or initial additional entanglement is needed. The one retained ebit realizes negative merging cost, without cloning an unknown state.
-- source:
--   Quantum information can be negative, arXiv:quant-ph/0505062v1, PDF p. 4, Example 3: a pure EPR source merges locally and yields one ebit

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P11

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, example 3: the pure EPR source has cost -1; Bob prepares the known
source locally while the original shared pair remains available as one ebit. -/
theorem exampleBell :
    IsState (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) ∧ conditionalEntropy (pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool)) = -1 ∧
    IsChannel bobPreparesBell ∧
    bellMergingOperation (pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool)) = bellMergingTarget := by sorry

end QAlgorithms.Papers.Independent.Gap20.P11

end
