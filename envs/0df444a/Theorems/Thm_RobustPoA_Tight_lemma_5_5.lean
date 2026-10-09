-- Prove2me | Theorems.Thm_RobustPoA_Tight_lemma_5_5
-- name    : RobustPoA.Tight.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:45.187103+00:00
-- url     : https://prove2.me/theorems/41ff279d-e56f-4cd1-a03c-f23122f58bfa
-- title:
--   Lemma 5.5, p. 27 — necessary condition for a nonattained γ(C,n)
-- statement:
--   Let $\mathcal C$ be a nonempty finite set of strictly positive, nondecreasing cost functions and $n\ge1$. If no pair in $\mathcal A(\mathcal C,n)$ attains $\gamma(\mathcal C,n)$, then some $c\in\mathcal C$ satisfies both
--
--   $$\gamma(\mathcal C,n)=\frac{c(n)n}{c(1)},\qquad c(n)n<c(n+1).$$
--
--   The two conclusions identify the value and a strict growth condition in the nonattainment case.
--
--   **Formalization Note** Nonemptiness comes from the standing assumption of §5.1; it is required because the conclusion selects a member of $\mathcal C$.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Lemma 5.5, p. 27, equations (46)–(47)

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

open scoped ENNReal

/-- Lemma 5.5, p. 27: when the finite smoothness infimum is not attained, a cost
function satisfies the paper's identity (46) and strict inequality (47). -/
theorem lemma_5_5 (C : Set (ℕ → ℝ)) (hfinite : C.Finite) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c ∧ IsStrictlyPos c) (n : ℕ) (hn : 1 ≤ n)
    (hnot : ∀ p ∈ smoothParamsN C n,
      ENNReal.ofReal (p.1 / (1 - p.2)) ≠ gammaN C n) :
    ∃ c ∈ C,
      gammaN C n = ENNReal.ofReal (c n * (n : ℝ) / c 1) ∧
      c n * (n : ℝ) < c (n + 1) := by sorry

end RobustPoA.Tight
