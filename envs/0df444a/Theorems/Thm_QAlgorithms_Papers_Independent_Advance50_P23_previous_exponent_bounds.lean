-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_previous_exponent_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.previous_exponent_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:49:08.66398+00:00
-- url     : https://prove2.me/theorems/42c48256-56c9-46cc-ad54-24cca4bc2d94
-- title:
--   Earlier book leakage exponent bounds
-- statement:
--   Let $W_E$ be a normalized finite cq family with input law $P_X$. For positive sequences $M_n,L_n$ and laws $P_{L_n}$ with $H_2(P_{L_n})\ge nR$, $R\ge0$, both actual iid-table ensemble mean Holevo leakage $a_n$ and full trace leakage $b_n$ satisfy $\liminf_n[-\log a_n/n]\ge e_{old}$ and $\liminf_n[-\log b_n/n]\ge e_{old}$, where $e_{old}=\sup_{0\le s\le1}s(R-I_s(W_E,P_X))/(2(1+s))$. Logarithms are natural and zero leakage has infinite decay exponent.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 15, Unnumbered p.15: earlier book exponent bounds

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

/-- PDF p.15: the earlier lower bounds of both ensemble exponents. Printed ordinary
limits are changed to extended liminf for exactly the same reason as the main
exponent item: arbitrary auxiliary laws need not have convergent decay rates. -/
theorem previous_exponent_bounds [Nonempty X] [Nonempty E]
    (WE : X → Matrix E E ℂ) (hE : hayashiIsCQ WE) (PX : X → ℝ) (hPX : IsLaw PX)
    (M L : ℕ → ℕ) (hM : ∀ n, 0 < M n) (hL : ∀ n, 0 < L n)
    (PL : (n : ℕ) → Fin (L n) → ℝ) (hPL : ∀ n, IsLaw (PL n))
    (R : ℝ) (hR : 0 ≤ R) (hentropy : ∀ n, n * R ≤ hayashiRenyiEntropy 1 (PL n)) :
    (previousExponent R WE PX : EReal) ≤ lowerExponent (fun n => ensembleInfo (M n) (L n)
      (productOutput n WE) (hayashiProductLaw n PX) (PL n)) ∧
    (previousExponent R WE PX : EReal) ≤ lowerExponent (fun n => ensembleTrace (M n) (L n)
      (productOutput n WE) (hayashiProductLaw n PX) (PL n)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
