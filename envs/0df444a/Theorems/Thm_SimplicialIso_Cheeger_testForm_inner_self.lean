-- Prove2me | Theorems.Thm_SimplicialIso_Cheeger_testForm_inner_self
-- name    : SimplicialIso.Cheeger.testForm_inner_self
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:00.842206+00:00
-- url     : https://prove2.me/theorems/6016db95-1a3e-439d-887f-a50c77121527
-- title:
--   §4.1, p. 13 — the denominator: ⟨f, f⟩ = n ∏_{i=0}^d |A_i|
-- statement:
--   Let $d\ge1$ and let $A_0,\dots,A_d$ be a partition of the $n$-element vertex set into nonempty sets, and let $f$ be the test form (4.1). On the complete $(d-1)$-skeleton,
--   $$\langle f,f\rangle=\sum_{\sigma\in X^{d-1}}f(\sigma)^2=\sum_{i=0}^d\Big(\prod_{j\ne i}|A_j|\Big)|A_i|^2=n\prod_{i=0}^d|A_i| .$$
--   This is the denominator of the Rayleigh quotient in (4.2).
--
--   **Formalization Note.** The sum runs over all $d$-element vertex sets, which are exactly the $(d-1)$-cells because the skeleton is complete. $d\ge1$ is a disclosed addition.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 13, §4.1, "The denominator is ⟨f, f⟩ = … = n ∏_{i=0}^d |A_i|"

import Mathlib
import Definitions.Def_SimplicialIso_Cheeger_Setting
import Definitions.Def_SimplicialIso_Cheeger_TestForm

namespace SimplicialIso.Cheeger

theorem testForm_inner_self (n d : ℕ) (hd : 1 ≤ d) (A : Fin (d + 1) → Finset (Fin n))
    (hA : IsPartition A) :
    inner ℝ (testForm A) (testForm A) = (n : ℝ) * ∏ i, ((A i).card : ℝ) := by sorry

end SimplicialIso.Cheeger
