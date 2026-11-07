-- Prove2me | Theorems.Thm_QuasiStrictNE_nash_ppad_hard
-- name    : QuasiStrictNE.nash_ppad_hard
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:09.096428+00:00
-- url     : https://prove2.me/theorems/a14339e5-2e7a-46b7-9f58-24e9819edc3f
-- title:
--   p.19 — [CDT09]: every PPAD problem reduces to bimatrix Nash
-- statement:
--   Every search problem in PPAD reduces, by a polynomial-time search reduction, to the problem Nash of computing an exact rational Nash equilibrium of a rational bimatrix game $(A,B)$ with $m,n\ge 1$. This is the hardness half of the PPAD-completeness of bimatrix Nash equilibria by Chen, Deng and Teng [CDT09], used in the paper's proof of Theorem 1.
--
--   Differences from the source:
--   - reading: PPAD = total search problems reducible to End-of-Line, End-of-Line described in words (p.8) → PPAD = {Q | Q total ∧ Q ≤ₚ EndOfLine}, End-of-Line in the circuit form P(0ⁿ) = 0ⁿ ≠ S(0ⁿ), answers x with P(S(x)) ≠ x or S(P(x)) ≠ x ≠ 0ⁿ; reason: the standard Daskalakis–Goldberg–Papadimitriou formalization of the paper's verbal definition; reductions are the paper's p.8 search reductions
--   - encoding: computing an equilibrium of a bimatrix game with payoffs in Q → instances are codes of rational games with m, n ≥ 1, answers codes of exact rational strategy pairs (encRatRect, encRatVec); reason: Δ0 is empty (p.4, k ≥ 1); exact rational answers are the paper's (p.19 outputs the rational pair (pr, qs)); the encodings change no instance
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 1, p.19 ([CDT09])

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_QuasiStrictNE_Nash
import Definitions.Def_QuasiStrictNE_PPAD

namespace QuasiStrictNE

/-- **Hardness of bimatrix Nash equilibria (Chen–Deng–Teng)** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 1, p.19: "For
hardness, use PPAD-completeness of computing a bimatrix Nash equilibrium by [CDT09]"; §1, p.2).

Every search problem in PPAD reduces, by a polynomial-time search reduction, to the problem Nash of
computing an exact rational Nash equilibrium of a rational bimatrix game.

**Formalization Note** This is the hardness half of [CDT09], cited by the paper; PPAD is the paper's
class (p.8). -/
theorem nash_ppad_hard : ∀ R ∈ PPAD, CardinalMatching.SearchReduces R Nash := by sorry

end QuasiStrictNE
