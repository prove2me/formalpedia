-- Prove2me | Theorems.Thm_SionMinimax_KKM_remark_3_6
-- name    : SionMinimax.KKM.remark_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:42.159164+00:00
-- url     : https://prove2.me/theorems/a825cddc-c886-437d-bc31-f0a1c477c328
-- title:
--   Remark 3.6, p. 174 — a quasi-concave-convex f on [0,1]² with f(·, 1) not u.s.c. has sup inf f = 0 and inf sup f = 1
-- statement:
--   Let $M = N = [0,1]$ and define $f : M \times N \to \{0, 1\}$ by
--
--   $$f(\mu, \nu) = \begin{cases} 0 & \text{if } 0 \le \mu < \tfrac12 \text{ and } \nu = 0, \text{ or } \tfrac12 \le \mu \le 1 \text{ and } \nu = 1, \\ 1 & \text{otherwise.} \end{cases}$$
--
--   Then:
--
--   1. for each $\nu \in [0,1]$, $f(\cdot, \nu)$ is quasi-concave on $[0,1]$;
--   2. for each $\mu \in [0,1]$, $f(\mu, \cdot)$ is quasi-convex on $[0,1]$;
--   3. for each $\mu \in [0,1]$, $f(\mu, \cdot)$ is lower semicontinuous on $[0,1]$;
--   4. $f(\cdot, 1)$ is **not** upper semicontinuous on $[0,1]$;
--   5. $\sup_{\mu \in M} \inf_{\nu \in N} f(\mu, \nu) = 0$ and $\inf_{\nu \in N} \sup_{\mu \in M} f(\mu, \nu) = 1$.
--
--   The example shows that in Sion's minimax theorem (Theorem 3.4) the upper semicontinuity in the first variable cannot simply be dropped, even for compact convex subsets of the real line: all other hypotheses hold and the minimax equality fails.
--
--   **Formalization Note** The page's condition "$0\le\mu<1/2$ and $\nu=0$ or $1/2\le\mu\le1$ and $\nu=1$" is read with "and" binding tighter than "or". The suprema and infima are taken over the subtype $[0,1]$ and computed in the extended reals `EReal` through the coercion of the real values. Only the checkable claims about the example are formalized; the informal assertion that the semicontinuity condition "cannot be removed nor appreciably weakened" is not a mathematical statement and is left out.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 174 (PDF p. 5), Remark 3.6

import Mathlib

namespace SionMinimax.KKM
theorem remark_3_6 :
    let f : ℝ → ℝ → ℝ := fun μ ν =>
      if (0 ≤ μ ∧ μ < 1 / 2 ∧ ν = 0) ∨ (1 / 2 ≤ μ ∧ μ ≤ 1 ∧ ν = 1) then 0 else 1
    (∀ ν ∈ Set.Icc (0 : ℝ) 1, QuasiconcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun μ => f μ ν)) ∧
    (∀ μ ∈ Set.Icc (0 : ℝ) 1, QuasiconvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun ν => f μ ν)) ∧
    (∀ μ ∈ Set.Icc (0 : ℝ) 1, LowerSemicontinuousOn (fun ν => f μ ν) (Set.Icc (0 : ℝ) 1)) ∧
    ¬ UpperSemicontinuousOn (fun μ => f μ 1) (Set.Icc (0 : ℝ) 1) ∧
    (⨆ μ : Set.Icc (0 : ℝ) 1, ⨅ ν : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 0 ∧
    (⨅ ν : Set.Icc (0 : ℝ) 1, ⨆ μ : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 1 := by sorry
end SionMinimax.KKM
