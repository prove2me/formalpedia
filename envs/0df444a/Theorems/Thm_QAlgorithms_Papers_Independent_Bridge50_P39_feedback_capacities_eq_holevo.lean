-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P39_feedback_capacities_eq_holevo
-- name    : QAlgorithms.Papers.Independent.Bridge50.P39.feedback_capacities_eq_holevo
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:52:34.26341+00:00
-- url     : https://prove2.me/theorems/6bc3e1b5-9abe-4483-93bd-7d4de1893901
-- title:
--   Both operational classical feedback capacities equal Holevo information
-- statement:
--   Let $\mathcal N:A\to B$ be a quantum channel between positive, finite-dimensional complex Hilbert spaces. Define $C_{\mathrm{FB}}(\mathcal N)$ as the supremum of nonnegative rates achievable by sequences of actual classical-feedback codes with vanishing uniform-message average decoding error. At each positive blocklength the code uses the same memoryless forward channel once per round, has arbitrary finite local quantum memories, no initially shared entanglement or message-dependent Bob seed, noiseless Bob-to-Alice classical feedback including $X_0$, and a final finite-message decoding POVM. The rate of an $n$-use, $L$-message code is $\log_2 L/n$; achievable rate is an eventual lower rate up to every positive tolerance.
--
--   Define $C_{\mathrm{FB,sep}}(\mathcal N)$ by the same operational criterion, restricting every actual conditional encoded state, for each message and past transcript before every individual forward use, to be fully separable across retained Alice memory, current input and Bob memory. Let $\chi(\mathcal N)$ be the ordinary single-use output Holevo information, optimized over all finite mixed-state input ensembles, with base-two entropy. Then both equalities hold:
--
--   $$
--   \mathcal N\text{ entanglement-breaking}\ \Longrightarrow\ C_{\mathrm{FB}}(\mathcal N)=\chi(\mathcal N),\qquad
--   C_{\mathrm{FB,sep}}(\mathcal N)=\chi(\mathcal N)\quad\text{for every }\mathcal N.
--   $$
--
--   The capacities are defined by communication protocols rather than by entropy. These equalities contain achievability as well as the weak-converse upper bounds; the separable restriction is imposed before every single channel use, not only between larger entangled blocks.
-- source:
--   Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels, arXiv:1506.02228v4, PDF p. 18, Corollary 8

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P39

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD tensorAction)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Support50.P19
  (channelInformation informationRadius expTwo)

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- PDF p.18, Corollary 8 (reproducing BN05): BOTH operational capacity equalities.
The separable-input capacity enforces separability before every single forward use;
unrestricted block encodings are not substituted for this resource class. -/
theorem feedback_capacities_eq_holevo [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) :
    (IsEB N → singleUseFeedbackCapacity N false = ENNReal.ofReal (channelHolevo N)) ∧
    singleUseFeedbackCapacity N true = ENNReal.ofReal (channelHolevo N) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P39

end
