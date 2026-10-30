-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P04_moreCapable_strictlyBroader
-- name    : QAlgorithms.Papers.Independent.Advance50.P04.moreCapable_strictlyBroader
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:29:05.279117+00:00
-- url     : https://prove2.me/theorems/aca1bb8b-a1c6-4d9b-84f0-d73f5c01cfef
-- title:
--   Unnumbered: more capable is strictly broader than less noisy
-- statement:
--   There exist positive integers $a,b,e$ and an isometry $U:\mathbb C^a\to\mathbb C^b\otimes\mathbb C^e$ defining complementary channels $N_B(\rho)=\operatorname{Tr}_E(U\rho U^*)$ and $N_E(\rho)=\operatorname{Tr}_B(U\rho U^*)$ such that
--
--   $$N_B\text{ is more capable and is not less noisy}. $$
--
--   Here more capable means $Q(N_E)=0$, and less noisy means $C_p(N_E)=0$, for the unassisted regularized quantum and private capacities. Together with the inclusion of less noisy channels in more capable channels, this proves strict containment. The paper obtains the witness using the existence result cited as [18]; it supplies neither an explicit example nor numerical capacities.
-- source:
--   Private and Quantum Capacities of More Capable and Less Noisy Quantum Channels, arXiv:1110.5746v3, PDF p. 4, Section III, strict inclusion

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P04

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel dilationPower
    maximumCoherentInformation IsDegradable)

open QAlgorithms.Papers.Independent.Support50.P01 (ConjugateDegradable)

open QAlgorithms.Papers.Independent.Information100.P56 (average)

open QAlgorithms.Papers.Independent.Dependency50.P48
  (holevoInformation privateMaximum regularizedCoherentInformation)

open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B E : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E]

variable {a b e : ℕ}

/-- Section III, PDF p.4: strictness witness obtained using the cited existence
result [18], rather than a newly constructed explicit example in this paper. -/
theorem moreCapable_strictlyBroader :
    ∃ a b e : ℕ, 0 < a ∧ 0 < b ∧ 0 < e ∧
      ∃ U : Matrix (Fin b × Fin e) (Fin a) ℂ,
        IsIsometry U ∧ MoreCapable U ∧ ¬ LessNoisy U := by sorry

end QAlgorithms.Papers.Independent.Advance50.P04

end
