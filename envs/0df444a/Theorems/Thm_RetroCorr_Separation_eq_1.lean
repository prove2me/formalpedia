-- Prove2me | Theorems.Thm_RetroCorr_Separation_eq_1
-- name    : RetroCorr.Separation.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:27.446042+00:00
-- url     : https://prove2.me/theorems/0c813afb-3a62-4602-860a-fa7b62718102
-- title:
--   Eq. (1), p. 2 — the one-shot Holevo capacity of R_{2,2} is 1 + (π²/18 − 5/6)/ln 2 = 0.5888
-- statement:
--   Let $S=R_{2,2}$ be the standard retrocorrectable channel with qubit control and qubit data, whose classical flag $k=(B,U_1,U_2)$ consists of a Haar-random basis $B$ of $\mathbb C^2$ and independent Haar-random $U_1,U_2\in U(2)$. Its one-shot Holevo capacity, in bits, with the flag as part of the output and the supremum taken over all finite ensembles of (possibly mixed or entangled) states of the two input qubits, is
--   $$C_H(R_{2,2})=1+\frac{\pi^2/18-5/6}{\ln 2},$$
--   and this number lies in $[0.58875,\,0.58885)$, i.e. it is $0.5888$ to four decimals.
--
--   The paper obtains (1) by noting that, by the symmetry of the channel, the optimum is attained by a uniform data ensemble with a fixed control input; that reduction is part of what this statement asserts, not an assumption of it.
--
--   **Formalization Note** `holevoCapacity (flagLaw 2 2) (retroBranch 2 2)` is the supremum in `ℝ≥0∞` of the flag-averaged Holevo quantity of `RetroCorr.Separation.Holevo`; the closed form is positive, so `ENNReal.ofReal` loses nothing. "ln 2" is `Real.log 2`.
--
--   Differences from the source:
--   - reading: "a random basis B" and "random unitaries U₁ … U_c" → B and U₁, U₂ independent and Haar distributed; reason: the caption names no distribution, and Haar is the reading under which (1) holds
--   - encoding: "C_H = … = 0.5888" → the closed form is exact, and 0.58875 ≤ value < 0.58885; reason: 0.5888 is a four-decimal rounding
--   - encoding: C_H with the classical control output included → the flag-average of the conditional Holevo quantities, in ℝ≥0∞; reason: the flag is independent of the input, so the two coincide (p. 2: "the control outputs do not contribute")
--   - encoding: basis B → a Haar unitary W whose columns are B, column phases revealed; reason: the phases are independent of the input and change no capacity
-- source:
--   Bennett, Devetak, Shor & Smolin, Inequalities and separations among assisted capacities of quantum channels, arXiv:quant-ph/0406086v1, p. 2, §2, eq. (1)

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel
import Definitions.Def_RetroCorr_Separation_Holevo

namespace RetroCorr.Separation
theorem eq_1 :
    holevoCapacity (flagLaw 2 2) (retroBranch 2 2) =
        ENNReal.ofReal (1 + (Real.pi ^ 2 / 18 - 5 / 6) / Real.log 2) ∧
      (0.58875 : ℝ) ≤ 1 + (Real.pi ^ 2 / 18 - 5 / 6) / Real.log 2 ∧
      1 + (Real.pi ^ 2 / 18 - 5 / 6) / Real.log 2 < 0.58885 := by sorry
end RetroCorr.Separation
