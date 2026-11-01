-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_pointwise_losr_simulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.pointwise_losr_simulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:15:56.322949+00:00
-- url     : https://prove2.me/theorems/589578ca-85db-47c7-8606-846b502edd7d
-- title:
--   Unnumbered result in Lemma 6 proof: pointwise LOSR simulation
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. For every WPICC wiring $W$ and every fixed no-signaling behavior $P$, there is an LOSR wiring $V$ such that
--
--   $$W(P)=V(P).$$
--
--   The quantifier order is $\forall W\,\forall P\,\exists V$: the simulator may depend on the fixed input box. This pointwise assertion does not identify the classes of operations. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 6, Proof of Lemma 6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P29

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P29

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel TwoLocalBoxes losrTransform
   correlationMixture)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

/-- PDF p.6, proof of Lemma 6: the simulating LOSR map may depend on this
specific input behavior, unlike an equality between classes of operations. -/
theorem pointwise_losr_simulation {s t : BellScenario} (w : BellOperation s t)
    (hw : IsWPICC w) (p : Behavior s) (hp : IsNS p) :
    ∃ v : BellOperation s t, IsLOSR v ∧ w p = v p := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
