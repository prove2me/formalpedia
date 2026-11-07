-- Prove2me | Theorems.Thm_QuasiStrictNE_nash_reduces_qsne
-- name    : QuasiStrictNE.nash_reduces_qsne
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:16.696234+00:00
-- url     : https://prove2.me/theorems/0bc6be80-3283-4653-999f-df634ffb9d93
-- title:
--   p.2 — Nash reduces to quasi-strict Nash
-- statement:
--   Computing an exact rational Nash equilibrium of a rational bimatrix game reduces, by a polynomial-time search reduction, to computing an exact rational quasi-strict Nash equilibrium of it. Hence the PPAD-hardness of computing a Nash equilibrium of a bimatrix game implies the PPAD-hardness of computing a quasi-strict equilibrium.
--
--   Differences from the source:
--   - encoding: computing an equilibrium of a bimatrix game with payoffs in Q → instances are codes of rational games with m, n ≥ 1, answers codes of exact rational strategy pairs (encRatRect, encRatVec); reason: Δ0 is empty (p.4, k ≥ 1); exact rational answers are the paper's (p.19 outputs the rational pair (pr, qs)); the encodings change no instance
--   - encoding: PPAD-hardness of Nash trivially implies PPAD-hardness of quasi-strict equilibria → the reduction Nash ≤ₚ QSNE that the implication rests on; reason: with nash_ppad_hard and transitivity of reductions this gives the hardness of QSNE; the reduction is what 'trivially implies' asserts
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §1, p.2

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_QuasiStrictNE_Nash
import Definitions.Def_QuasiStrictNE_QSNE

namespace QuasiStrictNE

/-- **Nash reduces to quasi-strict Nash** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, §1, p.2: "The PPAD-hardness of computing a Nash
equilibrium of a bimatrix game trivially implies PPAD-hardness of computing a quasi-strict equilibrium
in bimatrix games").

Computing an exact rational Nash equilibrium of a rational bimatrix game reduces, by a polynomial-time
search reduction, to computing an exact rational quasi-strict Nash equilibrium of it. -/
theorem nash_reduces_qsne : CardinalMatching.SearchReduces Nash QSNE := by sorry

end QuasiStrictNE
