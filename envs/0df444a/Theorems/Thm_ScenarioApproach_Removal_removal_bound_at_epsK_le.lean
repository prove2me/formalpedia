-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_removal_bound_at_epsK_le
-- name    : ScenarioApproach.Removal.removal_bound_at_epsK_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:55:57.282806+00:00
-- url     : https://prove2.me/theorems/1ceb02a1-2855-4e81-b9ed-df7d8a792fc9
-- title:
--   Section 3.3.1 — at $\varepsilon = \varepsilon_k$ of (1.9) the right-hand side of (3.13) is at most $\beta$
-- statement:
--   Let $N \ge 1$, $k \ge 1$, $d \ge 1$ be natural numbers and $\beta \in (0,1)$, and let $\varepsilon_k$ be given by formula (1.9):
--
--   $$
--   \varepsilon_k = \frac{k}{N} + \left[ \frac{\sqrt k}{N} + \frac{\sqrt k + 1}{N}\left( (d-1)\ln(k+d-1) + \frac{d-1}{\sqrt k} + \ln\frac1\beta \right) \right].
--   $$
--
--   If $\varepsilon_k \le 1$, then the right-hand side of (3.13) with $\varepsilon_k$ in place of $\varepsilon$ is at most $\beta$:
--
--   $$
--   \binom{k+d-1}{k} \sum_{i=0}^{k+d-1} \binom Ni \varepsilon_k^i (1-\varepsilon_k)^{N-i} \le \beta.
--   $$
--
--   Combined with Theorem 3.9 this gives Theorem 1.2.
--
--   **Formalization Note** The book does not state the condition $\varepsilon_k \le 1$; its derivation (3.15) uses $0 \le \varepsilon_k \le 1$ (nonnegativity of $(1-\varepsilon_k)^{N-i}$), and for $\varepsilon_k > 1$ the probabilistic conclusion of Theorem 1.2 is trivial. The ranges $N \ge 1$, $k \ge 1$ (the formula divides by $N$ and by $\sqrt k$), $d \ge 1$ and $\beta \in (0,1)$ are those of the page.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, pp. 47–48, Section 3.3.1 (opening sentence and Eq. (3.18))

import Mathlib
import Definitions.Def_ScenarioApproach_Removal_epsK

namespace ScenarioApproach.Removal

theorem removal_bound_at_epsK_le (N k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hε1 : epsK N k d β ≤ 1) :
    ((k + d - 1).choose k : ℝ) * ∑ i ∈ Finset.range (k + d),
      (N.choose i : ℝ) * epsK N k d β ^ i * (1 - epsK N k d β) ^ (N - i) ≤ β := by sorry

end ScenarioApproach.Removal
