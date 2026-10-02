-- Prove2me | Theorems.Thm_ScenarioApproach_Nonconvex_epsBeta_properties
-- name    : ScenarioApproach.Nonconvex.epsBeta_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T18:44:17.168252+00:00
-- url     : https://prove2.me/theorems/a7c8e590-f4ff-4ce5-af44-3c2b10ebd52a
-- title:
--   Eq. (8.16), arithmetic half — ε(k) lies in [0,1], ε(N) = 1, and the bound (8.15) equals β
-- statement:
--   Let $N\ge1$ and $\beta\in[0,1]$, and let $\epsilon(k)$ be the function (8.16),
--
--   $$
--   \epsilon(k)=\begin{cases}1 & k=N,\\ 1-\sqrt[N-k]{\beta/\big(N\binom Nk\big)} & k<N.\end{cases}
--   $$
--
--   Then
--
--   1. $\epsilon(k)\in[0,1]$ for every $k=0,1,\dots,N$;
--   2. $\epsilon(N)=1$;
--   3. $$\sum_{k=0}^{N-1}\binom Nk\,(1-\epsilon(k))^{N-k}=\beta.$$
--
--   Items 1 and 2 say that $\epsilon$ is an admissible level function for (8.15), and item 3 says that the right-hand side of (8.15) is then exactly $\beta$. Together with (8.15) this gives the confidence statement of (8.16).
--
--   **Formalization Note** The hypothesis $N\ge1$ is implicit on the page ($N$ is a sample size); for $N=0$ the sum in item 3 is empty and equals $0$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 105, Eq. (8.16) (with Eq. (8.15), p. 104)

import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_epsBeta

namespace ScenarioApproach.Nonconvex

/-- Eq. (8.16), arithmetic half. For `N ≥ 1` and `β ∈ [0, 1]`, the function `ε = epsBeta N β`
maps `{0, …, N}` into `[0, 1]`, satisfies `ε(N) = 1`, and makes the right-hand side of
(8.15) equal to `β`. -/
theorem epsBeta_properties (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∀ k ≤ N, epsBeta N β k ∈ Set.Icc (0 : ℝ) 1) ∧ epsBeta N β N = 1 ∧
      ∑ k ∈ Finset.range N, (N.choose k : ℝ) * (1 - epsBeta N β k) ^ (N - k) = β := by sorry

end ScenarioApproach.Nonconvex
