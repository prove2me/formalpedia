-- Prove2me | Theorems.Thm_PutermanMDP_Sensitive_lexicographic_characterization
-- name    : PutermanMDP.Sensitive.lexicographic_characterization
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:49.116889+00:00
-- url     : https://prove2.me/theorems/c31d416c-630e-4ca3-a3da-5eeb77781af6
-- title:
--   Theorem 10.2.3 — lexicographic characterization
-- statement:
--   Fix a deterministic stationary rule $d$ in a finite Markov decision process. Let $Y_n^{d^\infty}$ contain its Laurent coefficient columns $-1,0,\ldots,n$ in the interest parameter, and let $Y^{d^\infty}$ contain all these columns. For every integer $n\ge-1$,
--   $$d^\infty\text{ is }n\text{-discount optimal}\iff\forall\delta\in D,\ Y_n^{d^\infty}\ge_{\mathcal L}Y_n^{\delta^\infty}.$$
--   Also,
--   $$d^\infty\text{ is Blackwell optimal}\iff\forall\delta\in D,\ Y^{d^\infty}\ge_{\mathcal L}Y^{\delta^\infty}.$$
--   Here $D$ is the set of deterministic decision rules and the lexicographic comparison is rowwise. Optimality on the left still ranges over all history-dependent randomized competitors; only the coefficient comparison on the right is restricted to stationary rules.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 505 (PDF 521), Theorem 10.2.3; https://doi.org/10.1002/9780470316887

import Mathlib
import Definitions.Def_PutermanMDP_Sensitive_Coefficients

namespace PutermanMDP.Sensitive

theorem lexicographic_characterization {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    (M : Model S A) (d : DecisionRule M) :
    (∀ n : ℤ, -1 ≤ n →
      (NDiscountOptimal (stationary d) n ↔
        ∀ δ : DecisionRule M, LexGEThrough n (coefficient d) (coefficient δ))) ∧
    (BlackwellOptimal (stationary d) ↔
      ∀ δ : DecisionRule M, LexGE (coefficient d) (coefficient δ)) := by sorry

end PutermanMDP.Sensitive
