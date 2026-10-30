-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_classical_private_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.classical_private_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:48:27.323049+00:00
-- url     : https://prove2.me/theorems/14d25bef-69b1-4641-8084-1aa1508b2152
-- title:
--   Classical wiretap capacity single-letterization
-- statement:
--   For normalized finite cq output families that each commute pairwise, there is a finite stochastic auxiliary encoder $A$ attaining the maximum private information $v(A)=I(V;B)-I(V;E)$. Every such encoder $F$ satisfies $v(F)\le v(A)$; the operational private capacity equals $v(A)$, and $B_n/n=v(A)$ for every positive block length. Separate simultaneous diagonalization identifies these families with classical channels.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 14, Unnumbered p.14: classical single-letter wiretap capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF p.14: classical single-letter capacity, attributed to Csiszar and Korner [2].
Separate commuting output families are classical channels in fixed diagonalizing bases. -/
theorem classical_private_capacity [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE)
    (hcB : ∀ x y, WB x * WB y = WB y * WB x)
    (hcE : ∀ x y, WE x * WE y = WE y * WE x) :
    ∃ C : QAlgorithms.Papers.Independent.Information100.P56.Encoder X,
      wiretapCapacity WB WE =
        (QAlgorithms.Papers.Independent.Information100.P56.encoderValue WB WE C : EReal) ∧
      (∀ F : QAlgorithms.Papers.Independent.Information100.P56.Encoder X,
        QAlgorithms.Papers.Independent.Information100.P56.encoderValue WB WE F ≤
          QAlgorithms.Papers.Independent.Information100.P56.encoderValue WB WE C) ∧
      ∀ n : ℕ, 0 < n →
        QAlgorithms.Papers.Independent.Information100.P56.blockPrivate n WB WE / n =
          QAlgorithms.Papers.Independent.Information100.P56.encoderValue WB WE C := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
