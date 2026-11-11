-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_8_4
-- name    : SAInterp.Res2.theorem_8_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:37:55.253082+00:00
-- url     : https://prove2.me/theorems/9426589f-bcb9-4cfa-93ce-122091f7a2ea
-- title:
--   Theorem 8.4 — a length-s Resolution refutation of a width-w, n-variable CNF F gives a size-O(2^w n s) Res(2) refutation of F ∘ ⊕
-- statement:
--   There is a universal constant $C$ with the following property. Let $F$ be a CNF of width $w$ (the largest clause size) with $n$ variables, and suppose $F$ has a Resolution refutation of length $s$ (number of lines). Then $F\circ\oplus$ has a $\mathrm{Res}(2)$ refutation $\Pi$ with
--   $$\mathrm{size}(\Pi)\ \le\ C\cdot 2^w\,n\,s+C .$$
--   Resolution here is cut-only, with clauses as lines.
--
--   Differences from the source:
--   - reading: size O(2^w n s) → ≤ C · 2^w · n · s + C with one universal C; reason: O(·) with an explicit constant fixed before F; the additive C covers the degenerate F whose variables never occur (n = 0), where any refutation has positive size.
--   - reading: "n variables", "width-w", "length-s" → n = numVars F (variables occurring in F), w = cnfWidth F, s = number of lines; reason: the paper's parameters, at their tightest.
--   - reading: Res(2) size = total number of symbols → Σ over lines of (1 + literal occurrences); reason: within a constant factor of any symbol count, which the constant C absorbs.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 45 (PDF p. 47), Theorem 8.4

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_ResK

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- Theorem 8.4 (p. 45): there is a universal constant `C` such that, if `F` is a CNF of width
`w` with `n` variables and a Resolution refutation of length `s`, then `F ∘ ⊕` has a `Res(2)`
refutation of size `≤ C · 2^w · n · s + C`. -/
theorem theorem_8_4 :
    ∃ C : ℝ, ∀ (α : Type) (F : CNF α) (P : List (Clause α)), IsRefutation F P →
      ∃ Q : List (DNF (α ⊕ α)), IsResKRefutation 2 (xorCNF F) Q ∧
        (resKSize Q : ℝ) ≤
          C * ((2 : ℝ) ^ cnfWidth F * (numVars F : ℝ) * (P.length : ℝ)) + C := by sorry

end SAInterp.Res2
