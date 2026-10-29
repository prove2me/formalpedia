-- Prove2me | Theorems.Thm_PutermanMDP_Sensitive_finite_coefficient_determination
-- name    : PutermanMDP.Sensitive.finite_coefficient_determination
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:03.746395+00:00
-- url     : https://prove2.me/theorems/91ce8af9-82be-4294-af1d-2c965b183699
-- title:
--   Proposition 10.3.5 — finite coefficient determination
-- statement:
--   Let $\delta,d$ be deterministic decision rules in a finite Markov decision process. Suppose $P_d$ has $r$ recurrent classes and their Laurent coefficient vectors agree through the indicated order:
--   $$y_k^{\delta^\infty}=y_k^{d^\infty}\qquad(-1\le k\le |S|-r-1).$$
--   The printed proposition concludes
--   $$y_k^{\delta^\infty}=y_k^{d^\infty}\qquad\text{for every integer }k\ge-1.$$
--   This is the chapter's finite-determination claim. FINDINGS records a counterexample at $r=|S|$; the statement is preserved rather than silently adding a hypothesis.
--
--   **Formalization Note** The threshold uses integer subtraction and is $-1$ when $r=|S|$. There is no assumption that $P_\delta$ also has $r$ recurrent classes.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 518 (PDF 534), Proposition 10.3.5; https://doi.org/10.1002/9780470316887

import Mathlib
import Definitions.Def_PutermanMDP_Sensitive_Coefficients

namespace PutermanMDP.Sensitive

/-- Printed Proposition 10.3.5. The coefficient interval is closed at both ends:
when r = |S| it consists of the single index -1; when r = |S|-1 it is {-1, 0}.
The r=|S| boundary is disputed in FINDINGS. -/
theorem finite_coefficient_determination {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    (M : Model S A) (δ d : DecisionRule M) (r : ℕ)
    (hr : recurrentCount (policyMatrix d) = r)
    (heq : ∀ k ∈ Set.Icc (-1 : ℤ) ((Fintype.card S : ℤ) - (r : ℤ) - 1),
      coefficient δ k = coefficient d k) :
    ∀ k : ℤ, -1 ≤ k → coefficient δ k = coefficient d k := by sorry

end PutermanMDP.Sensitive
