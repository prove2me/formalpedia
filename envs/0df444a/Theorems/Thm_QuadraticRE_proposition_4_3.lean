-- Prove2me | Theorems.Thm_QuadraticRE_proposition_4_3
-- name    : QuadraticRE.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:12:08.223751+00:00
-- url     : https://prove2.me/theorems/780fec04-b441-4149-8409-3bcac4de7f50
-- title:
--   Proposition 4.3 — correctness: error $\le\frac72L2^{-h}$ for $j\ge1$, $\le7\cdot2^{-h}$ for $j=0$
-- statement:
--   For all integers $j\ge0$ and $h\ge3$, with $L=4^j$, and every $(a,b,c,d)\in\mathbb F_2^4$,
--   $$\Pr_R\bigl[\mathrm{Dec}_{j,h}(E_{j,h}(a,b,c,d;R))\neq abc+d\bigr]\le\begin{cases}\tfrac72\,L\,2^{-h},&j\ge1,\\[2pt]7\cdot2^{-h},&j=0,\end{cases}$$
--   the probability being over the uniform tape $R$.
--
--   Increasing $h$ makes the encoding arbitrarily reliable without changing its degree.
--
--   Differences from the source:
--   - encoding: 2^{−h} → (1/2)^h; reason: Lean notation; same number
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Proposition 4.3, p.18

import Mathlib
import Definitions.Def_QuadraticRE_encE

namespace QuadraticRE

/-- Proposition 4.3 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.18: the correctness of `E_{j,h}`, in both cases.

**Formalization Note.** `2^{−h}` is written `(1/2)^h`. -/
theorem proposition_4_3 (j h : ℕ) (hh : 3 ≤ h) (a b c d : F2) :
    (1 ≤ j → prob (fun R : Tape j h => decE j h (encE j h a b c d R) ≠ a * b * c + d)
        ≤ (7 / 2) * (4 ^ j : ℝ) * (1 / 2) ^ h) ∧
    (j = 0 → prob (fun R : Tape j h => decE j h (encE j h a b c d R) ≠ a * b * c + d)
        ≤ 7 * (1 / 2) ^ h) := by sorry

end QuadraticRE
