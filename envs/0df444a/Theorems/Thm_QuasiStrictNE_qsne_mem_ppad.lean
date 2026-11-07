-- Prove2me | Theorems.Thm_QuasiStrictNE_qsne_mem_ppad
-- name    : QuasiStrictNE.qsne_mem_ppad
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:04.340419+00:00
-- url     : https://prove2.me/theorems/1760a8f8-58d2-4743-aa8d-36e5f38f7e88
-- title:
--   p.19 — computing a quasi-strict equilibrium is in PPAD
-- statement:
--   The search problem QSNE — given a rational bimatrix game $(A,B)$ with $m,n\ge 1$, find an exact rational quasi-strict Nash equilibrium — belongs to PPAD: every instance has an answer, and QSNE reduces to End-of-Line by a polynomial-time search reduction.
--
--   Differences from the source:
--   - reading: PPAD = total search problems reducible to End-of-Line, End-of-Line described in words (p.8) → PPAD = {Q | Q total ∧ Q ≤ₚ EndOfLine}, End-of-Line in the circuit form P(0ⁿ) = 0ⁿ ≠ S(0ⁿ), answers x with P(S(x)) ≠ x or S(P(x)) ≠ x ≠ 0ⁿ; reason: the standard Daskalakis–Goldberg–Papadimitriou formalization of the paper's verbal definition; reductions are the paper's p.8 search reductions
--   - encoding: computing an equilibrium of a bimatrix game with payoffs in Q → instances are codes of rational games with m, n ≥ 1, answers codes of exact rational strategy pairs (encRatRect, encRatVec); reason: Δ0 is empty (p.4, k ≥ 1); exact rational answers are the paper's (p.19 outputs the rational pair (pr, qs)); the encodings change no instance
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), proof of Theorem 1, p.19

import Mathlib
import Definitions.Def_QuasiStrictNE_QSNE
import Definitions.Def_QuasiStrictNE_PPAD

namespace QuasiStrictNE

/-- **Membership: computing a quasi-strict equilibrium is in PPAD** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, proof of Theorem 1, p.19: "For
membership, using Theorem 3, we can obtain a fixed point (x̄, ȳ) of T′, which is rational and can be
computed in PPAD. … As the proof of Theorem 5 shows, (pr, qs) is a quasi-strict Nash equilibrium").

The search problem QSNE (given a rational bimatrix game, find an exact rational quasi-strict Nash
equilibrium) belongs to PPAD: every instance has an answer, and QSNE reduces to End-of-Line by a
polynomial-time search reduction. -/
theorem qsne_mem_ppad : QSNE ∈ PPAD := by sorry

end QuasiStrictNE
