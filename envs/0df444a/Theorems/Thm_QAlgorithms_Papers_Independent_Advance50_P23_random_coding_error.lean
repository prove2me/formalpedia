-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_random_coding_error
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.random_coding_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:52:42.803985+00:00
-- url     : https://prove2.me/theorems/27675a3b-c3bb-4eb0-801f-fd3c400cfadf
-- title:
--   Iid random coding error bound with nonuniform auxiliary law
-- statement:
--   For positive $M,L$, input law $P_X$, auxiliary law $P_L$ and normalized Bob cq family $W_B$, sample each table entry $c(l,m)$ independently with law $P_X$. There are normalized word POVMs $D^c_{l,m}$ and message codes with encoder $\Gamma^c_m(x)=\sum_{l:c(l,m)=x}P_L(l)$ and decoder $\sum_l D^c_{l,m}$. For the same choices and every $0\le t\le1$, both the mean full-word error with prior $P_L(l)/M$ and the mean grouped-message error are at most $4(ML)^t e^{-tI_{-t}(W_B,P_X)}$, with value $4$ at $t=0$.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 10, Cited (63): cq random-coding error exponent

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

/-- PDF pp.9–10, (63): iid codebook decoding, including the nonuniform prior
PL(l)/M on each word (l,m). Word POVMs are selected before all exponent parameters;
the message decoder groups their effects and uses precisely the table encoder. -/
theorem random_coding_error [Nonempty X] [Nonempty B]
    (WB : X → Matrix B B ℂ) (hB : hayashiIsCQ WB) (M L : ℕ) (hM : 0 < M) (hL : 0 < L)
    (PX : X → ℝ) (hPX : IsLaw PX) (PL : Fin L → ℝ) (hPL : IsLaw PL) :
    ∃ word : (Fin L → Fin M → X) → Fin L → Fin M → Matrix B B ℂ,
    ∃ C : (Fin L → Fin M → X) → WiretapCode X B M,
      (∀ c, IsPOVM (fun i : Fin L × Fin M => word c i.1 i.2)) ∧
      (∀ c, (C c).encoder = tableEncoder PL c ∧ ∀ m, (C c).decoder m = ∑ l, word c l m) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∑ c, bookLaw PX c * ∑ l, ∑ m,
          PL l / M * (1 - effectProb (word c l m) (WB (c l m)))) ≤
            4 * hayashiReliability M L t WB PX ∧
        (∑ c, bookLaw PX c * hayashiCodeError WB (C c)) ≤
          4 * hayashiReliability M L t WB PX := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
