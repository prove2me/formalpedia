-- Prove2me | Theorems.Thm_RhinViola_nonzeroDeterminantSeparation
-- name    : RhinViola.nonzeroDeterminantSeparation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T07:32:53.473012+00:00
-- url     : https://prove2.me/theorems/21bda80b-41d4-4ea7-9077-bce0bc778e13
-- title:
--   Integer-determinant separation step in the Rhin–Viola irrationality criterion
-- statement:
--   Let f=a-bα be an integer linear form. If q is positive, q|f|≤1/2, and the integer determinant qa-pb is nonzero, then |qa-pb|≥1 forces 1/2≤|b| q |α-p/q|. This is the nonzero-determinant branch of Rhin and Viola's abstract irrationality-measure criterion.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4. This theorem isolates the D=qa_n-pb_n≠0 branch used in the proof of the irrationality-measure criterion underlying RhinViola.zetaTwoIrrationalityBound (bb98b323-fe68-49fe-a97c-b06c6157899b).

import Mathlib.Tactic
import Mathlib.Data.Int.Cast.Lemmas

theorem RhinViola.nonzeroDeterminantSeparation
    (α f : ℝ) (a b p : ℤ) (q : ℕ)
    (hq : 0 < q)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hsmall : (q : ℝ) * |f| ≤ (1 : ℝ) / 2)
    (hdet : (q : ℤ) * a ≠ p * b) :
    (1 : ℝ) / 2 ≤ |(b : ℝ)| * (q : ℝ) *
      |α - (p : ℝ) / (q : ℝ)| := by sorry
