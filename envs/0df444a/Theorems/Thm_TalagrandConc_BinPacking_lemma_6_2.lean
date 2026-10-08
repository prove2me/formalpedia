-- Prove2me | Theorems.Thm_TalagrandConc_BinPacking_lemma_6_2
-- name    : TalagrandConc.BinPacking.lemma_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:30.145976+00:00
-- url     : https://prove2.me/theorems/9791328f-fb31-4f76-a0ad-7d9d46ff9183
-- title:
--   Lemma 6.2 — B_N(x) ≤ a + 2‖x‖₂ f_c(A(a), x) + 1
-- statement:
--   Let $\Omega = [0,1]$, $a > 0$, and $A(a) = \{ y \in \Omega^N : B_N(y) \le a \}$, where $B_N$ is the bin packing number. Let $f_c(A,x)$ denote the convex hull distance of Section 4.1 and $\|x\|_2$ the Euclidean norm. Then for every $x \in \Omega^N$,
--   $$B_N(x) \le a + 2\,\|x\|_2\, f_c(A(a),x) + 1 . \tag{6.2}$$
--
--   This is the "crucial observation" of the chapter: it converts the convex hull distance from a level set of $B_N$ into a bound on $B_N$ itself, so that Talagrand's convex distance inequality can be applied.
--
--   **Formalization Note** The inequality is stated in $[0,+\infty]$, where $f_c(A(a),x) = +\infty$ if $A(a) = \emptyset$, with the convention $0 \cdot \infty = 0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 151, Lemma 6.2, Eq. (6.2)

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.BinPacking

open scoped ENNReal

/-- Talagrand (1995), p. 151, Lemma 6.2, Eq. (6.2): for `a > 0` and all `x ∈ Ω^N`,
`B_N(x) ≤ a + 2 ‖x‖₂ f_c(A(a), x) + 1`. Computed in `ℝ≥0∞` (`f_c = ⊤` when `A(a) = ∅`). -/
theorem lemma_6_2 {N : ℕ} (a : ℝ) (ha : 0 < a) (x : Fin N → unitInterval) :
    (binNumber x : ℝ≥0∞) ≤
      ENNReal.ofReal a + 2 * ENNReal.ofReal (l2Norm x) * convexDist (levelSet N a) x + 1 := by sorry

end TalagrandConc.BinPacking
