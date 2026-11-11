-- Prove2me | Theorems.Thm_QuadStatRE_Main_proposition_7_2
-- name    : QuadStatRE.Main.proposition_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:48:13.679321+00:00
-- url     : https://prove2.me/theorems/a8834a5b-a611-4c5f-92fe-0ab2b75c0461
-- title:
--   Proposition 7.2 — four levels enter the cubic regime: τ₄ < 3/50 < 1/16
-- statement:
--   For the iterated equality leakage $W_0$, $W_{r+1}=\mathcal A(W_r)$, with $\tau_r=\tau(W_r)$,
--   $$\tau_4<\frac3{50}<\frac1{16}.$$
--
--   Four RM steps bring the leakage of the basic gadget into the regime of Lemma 6.7.
--
--   Differences from the source:
--
--   - encoding: the iterated equality leakage W_r and τ_r = τ(W_r) → Wr r on the alphabet Omega r (G × F₂ at depth 0, Fin 15 → Omega r at depth r + 1); reason: the recursion of §5.2
--   - encoding: positions I = F₂⁴ ∖ {0} → Fin 15, position k the vector of binary digits of k + 1; reason: an enumeration of I; each nonzero vector occurs once
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 33, Proposition 7.2

import Mathlib
import Definitions.Def_QuadStatRE_Main_ChiSquare
import Definitions.Def_QuadStatRE_Main_Iterated
open QuadraticRE

namespace QuadStatRE.Main

/-- Proposition 7.2 (Four-level entry), p. 33: for the iterated equality leakage,
`τ₄ < 3/50 < 1/16`. -/
theorem proposition_7_2 :
    tau (Wr 4) < 3 / 50 ∧ (3 / 50 : ℝ) < 1 / 16 := by sorry

end QuadStatRE.Main
