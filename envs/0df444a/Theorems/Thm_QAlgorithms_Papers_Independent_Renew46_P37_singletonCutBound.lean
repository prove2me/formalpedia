-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_singletonCutBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.singletonCutBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:29:21.858252+00:00
-- url     : https://prove2.me/theorems/ded2f6fc-553d-41b6-a39d-732421322cc6
-- title:
--   Extraction bound at every singleton cut
-- statement:
--   Let a normalized pure state $\rho$ be shared by $n\ge2$ parties with nonzero finite local dimensions. Any finite adaptive local-instrument/public-communication protocol ending in classical outputs $X_1,\ldots,X_n$, with all public information in $\tau$, satisfies, for every party $i$,
--   $$\sum_\tau p(\tau)I(X_i:X_{-i}\mid\tau)\le S(\rho_i).$$
--   Here $\rho_i$ is the initial one-party reduced state and $X_{-i}$ denotes all other outputs.
--
--   The protocol remains local among all $n$ parties; the bound applies simultaneously to every singleton cut.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 12, §V.E, (72)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- §V.E, PDF p.12, (72): every singleton cut is bounded by its INITIAL
local entropy. The actual protocol stays local among all n parties. -/
theorem singletonCutBound {n : ℕ} (hn : 2 ≤ n) (s : FiniteState n)
    (hpure : QAlgorithms.Papers.Independent.Information100.P08.IsPure s.rho)
    (out : List (ℝ × FiniteState n)) (hprotocol : QLOPC s out)
    (hclassical : ∀ z ∈ out, 0 < z.1 → IsDiagonalOutput z.2) :
    ∀ i : Fin n, (out.map fun z => z.1 *
      lawCMI (readout z.2) {i} (Finset.univ.erase i) ∅).sum ≤ qH s {i} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
