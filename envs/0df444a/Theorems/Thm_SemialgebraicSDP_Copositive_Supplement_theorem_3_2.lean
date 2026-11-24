-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_Supplement_theorem_3_2
-- name    : SemialgebraicSDP.Copositive.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:44:46.559433+00:00
-- url     : https://prove2.me/theorems/fb692cda-2688-4d6c-a64a-0b32dbd01325
-- title:
--   Theorem 3.2 (corrected: boundary cases) — full Hilbert classification of nonnegative and SOS forms
-- statement:
--   For $n,d\in\mathbb N$, write $P_{n,2d}$ for the nonnegative homogeneous real forms of degree $2d$ and $\Sigma_{n,2d}$ for the finite sums of squares of degree-$d$ forms. Then
--   $$\Sigma_{n,2d}\subseteq P_{n,2d},\qquad \Sigma_{n,2d}=P_{n,2d}\ \Longleftrightarrow\ n\le2\ \text{or}\ d\le1\ \text{or}\ (n,d)=(3,2).$$
--   This includes the bivariate, quadratic and ternary-quartic cases and the full only-if direction. It is a companion theorem, with no claim that it is used to prove the published goal.
--
--   **Formalization Note** The printed classification omits one-variable forms and constant forms. For example, every nonnegative one-variable quartic is $c x^4=(\sqrt c\,x^2)^2$ for $c\ge0$, although $(n,m)=(1,4)$ is absent from its list. The corrected classification restores these cases, including zero-variable forms, with no dimension restriction. The degree is parameterized as $m=2d$: the source's summands of degree $m/2$ specify its even-degree setting; this item makes no claim about a half-integral homogeneous degree.
--
--   Differences from the source:
--   - correction: equality only for n=2, m=2, or (n,m)=(3,4) → equality for n≤2, d≤1, or (n,d)=(3,2), with m=2d; reason: one-variable forms and constants also have equality; n=0 gives constants or the zero space and is included.
--   - reading: forms of degree m, squares of forms of degree m/2 → even degree m=2d and homogeneous degree-d summands; reason: makes explicit the integral half-degree implicit in the source definition, rather than using truncated natural division.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 298, Theorem 3.2 (Hilbert)

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Supplement_HilbertCones

namespace SemialgebraicSDP.Copositive.Supplement

/-- Hilbert's classification (Theorem 3.2), with the missing boundary cases restored.
The degree is 2d, as required by the degree-d summands in the source definition. -/
theorem theorem_3_2 (n d : ℕ) :
    sosForms n d ⊆ nonnegativeForms n (2 * d) ∧
    (sosForms n d = nonnegativeForms n (2 * d) ↔
      n ≤ 2 ∨ d ≤ 1 ∨ (n = 3 ∧ d = 2)) := by sorry

end SemialgebraicSDP.Copositive.Supplement
