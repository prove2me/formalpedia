-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_commuting_renyi_comparison
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.commuting_renyi_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:46:17.660696+00:00
-- url     : https://prove2.me/theorems/87562a3a-7ce9-483e-9805-4078c807386a
-- title:
--   Commuting Renyi information comparison
-- statement:
--   For a normalized finite cq ensemble $(W,P)$ with pairwise commuting outputs and $0\le s<1$, $I_s(W,P)\le I^G_{s/(1-s)}(W,P)$. Here $I_s$ is Petz information, $I_s^G$ is Gallager information, and both at zero are Holevo information. The positive denominator is $1-s$.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 5, Lemma 2, (36): commuting comparison

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

/-- PDF p.5, Lemma 2, (36), cited to [20,(16)]. The denominator is positive
on [0,1); the two continuous zero branches agree. -/
theorem commuting_renyi_comparison [Nonempty X] [Nonempty E]
    (W : X → Matrix E E ℂ) (hW : hayashiIsCQ W) (P : X → ℝ) (hP : IsLaw P)
    (hcomm : ∀ x y, W x * W y = W y * W x)
    (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    petzInfo s W P ≤ gallagerInfo (s / (1 - s)) W P := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
