-- Prove2me | Theorems.Thm_QuasiStrictNE_theorem_1
-- name    : QuasiStrictNE.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:53.590079+00:00
-- url     : https://prove2.me/theorems/938b92e3-aaa4-4eb1-b121-5d1968a3f49d
-- title:
--   Theorem 1 — computing a quasi-strict Nash equilibrium of a bimatrix game is PPAD-complete
-- statement:
--   Computing a quasi-strict Nash equilibrium of a bimatrix game is PPAD-complete. Precisely, the search problem QSNE — given a rational bimatrix game $(A,B)\in\mathbb Q^{m\times n}\times\mathbb Q^{m\times n}$ with $m,n\ge 1$, find rational $x\in\Delta_m$, $y\in\Delta_n$ with
--   $$
--   \mathrm{supp}(x)=BR_1(y),\qquad \mathrm{supp}(y)=BR_2(x)
--   $$
--   — satisfies
--
--   1. **membership**: QSNE is total and reduces to End-of-Line by a polynomial-time search reduction;
--   2. **hardness**: every problem in PPAD reduces to QSNE by a polynomial-time search reduction.
--
--   Differences from the source:
--   - reading: PPAD = total search problems reducible to End-of-Line, End-of-Line described in words (p.8) → PPAD = {Q | Q total ∧ Q ≤ₚ EndOfLine}, End-of-Line in the circuit form P(0ⁿ) = 0ⁿ ≠ S(0ⁿ), answers x with P(S(x)) ≠ x or S(P(x)) ≠ x ≠ 0ⁿ; reason: the standard Daskalakis–Goldberg–Papadimitriou formalization of the paper's verbal definition; reductions are the paper's p.8 search reductions
--   - encoding: computing an equilibrium of a bimatrix game with payoffs in Q → instances are codes of rational games with m, n ≥ 1, answers codes of exact rational strategy pairs (encRatRect, encRatVec); reason: Δ0 is empty (p.4, k ≥ 1); exact rational answers are the paper's (p.19 outputs the rational pair (pr, qs)); the encodings change no instance
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 1, p.2 (restated and proved p.19)

import Mathlib
import Definitions.Def_QuasiStrictNE_QSNE
import Definitions.Def_QuasiStrictNE_PPADComplete

namespace QuasiStrictNE

/-- **Theorem 1** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, Theorem 1, p.2, restated and proved on p.19: "Computing a quasi-strict
Nash equilibrium of a bimatrix game is PPAD-complete").

The search problem QSNE — given a rational bimatrix game `(A, B)` with `m, n ≥ 1` pure strategies, find
an exact rational quasi-strict Nash equilibrium — is PPAD-complete: it is total and reduces to
End-of-Line (membership), and every problem of PPAD reduces to it (hardness).

**Formalization Note** PPAD is the paper's class (p.8): total search problems reducible to
End-of-Line, with End-of-Line in the circuit form of Daskalakis–Goldberg–Papadimitriou and
polynomial-time search reductions as defined on p.8 (`CardinalMatching.SearchReduces`). -/
theorem theorem_1 : PPADComplete QSNE := by sorry

end QuasiStrictNE
