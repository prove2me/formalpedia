-- Prove2me | Theorems.Thm_PBElicit_RandThresh_eq_6
-- name    : PBElicit.RandThresh.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:01.444105+00:00
-- url     : https://prove2.me/theorems/4afc1f4b-0140-43f0-8abe-4c435175ebff
-- title:
--   Eq. (6), p. 13 — the welfare of an alternative is sandwiched by the interval counts n^a_j
-- statement:
--   Let $m=2^K$ be the number of alternatives, $\vec v$ a normalized utility profile of $n$ voters, and $a$ an alternative. With $\ell_j=2^{j-1}/m^2$, $u_j=2^j/m^2$, $I_j=(\ell_j,u_j]$ and $n^a_j=|\{i: v_i(a)\in I_j\}|$ for $1\le j\le 2\log_2 m=2K$,
--   $$
--   \sum_{j=1}^{2\log m} n^a_j\,\ell_j\ \le\ \mathrm{sw}(a,\vec v)\ \le\ \frac{n}{m^2}+\sum_{j=1}^{2\log m} n^a_j\,u_j,
--   $$
--   where $\mathrm{sw}(a,\vec v)=\sum_{i\in N}v_i(a)$.
--
--   This discretizes the welfare of each alternative into geometric utility levels, which is what threshold approval votes at thresholds $\ell_j$ can observe.
--
--   **Formalization Note.** $m$ is `Fintype.card A`, assumed equal to $2^K$ as in the proof ("for ease of exposition, assume $m$ is a power of 2"); $\log$ is base $2$, so $2\log m=2K$.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), proof of Theorem 3.5, eq. (6), p. 13

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem eq_6 {n : ℕ} {A : Type*} [Fintype A] (v : Fin n → A → ℝ) (hv : IsUtilityProfile v)
    (m K : ℕ) (hA : Fintype.card A = m) (hmK : m = 2 ^ K) (a : A) :
    ∑ j ∈ Finset.Icc 1 (2 * K), (cnt v m a j : ℝ) * lo m j ≤ ∑ i, v i a ∧
      ∑ i, v i a ≤ (n : ℝ) / (m : ℝ) ^ 2 + ∑ j ∈ Finset.Icc 1 (2 * K), (cnt v m a j : ℝ) * up m j := by sorry

end PBElicit.RandThresh
