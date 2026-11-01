-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P29_wiring_inclusions_and_separation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P29.wiring_inclusions_and_separation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:14:25.394717+00:00
-- url     : https://prove2.me/theorems/d0f91863-13b5-4efc-82e2-5e02174432ca
-- title:
--   Unnumbered main result: LOSR inclusion and strict separation, (9),(11)
-- statement:
--   All Bell scenarios have independent finite, nonempty Alice and Bob input and output alphabets. A behavior is a nonnegative conditional output law normalized at every input pair; $\mathrm{NS}$ imposes both no-signaling marginal identities. Processing uses one initial box with rules and randomness fixed independently of the supplied behavior. For every pair of scenarios, every LOSR wiring is both a WPICC wiring and a global wiring. Moreover, there are scenarios and a WPICC wiring for which no LOSR wiring agrees on all no-signaling inputs:
--
--   $$\mathrm{LOSR}\subseteq\mathrm{WPICC},\qquad \mathrm{LOSR}\subseteq\mathrm{GW},\qquad\exists W\in\mathrm{WPICC}:W\notin\mathrm{LOSR}.$$
--
--   Strictness is existential over scenarios; no strict separation is asserted for degenerate fixed scenarios. WPICC uses Appendix A’s fixed no-preparation LOSR branch and random adaptive preparation branches in which at least one party measures before the final inputs.
-- source:
--   Nonlocality free wirings and the distinguishability between Bell boxes, arXiv:1611.06932v2, PDF p. 4, Equations (9),(11); strictness p.6

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

/-- PDF p.4, (9),(11), and p.6 strict separation: both inclusions hold in every
scenario pair, while strict LOSR/WPICC separation is existential over scenarios.
The witness is separated extensionally on the common NS domain. -/
theorem wiring_inclusions_and_separation :
    (∀ (s t : BellScenario) (w : BellOperation s t),
      IsLOSR w → IsWPICC w ∧ IsGW w) ∧
    (∃ (s t : BellScenario) (w : BellOperation s t),
      IsWPICC w ∧ ¬ HasLOSRRestriction w) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P29

end
