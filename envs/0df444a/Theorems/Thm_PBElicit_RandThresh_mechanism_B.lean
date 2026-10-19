-- Prove2me | Theorems.Thm_PBElicit_RandThresh_mechanism_B
-- name    : PBElicit.RandThresh.mechanism_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:32.657425+00:00
-- url     : https://prove2.me/theorems/91668b7f-b28a-4587-8493-c59e605c9df9
-- title:
--   Proof of Theorem 3.5, p. 14 — Mechanism B: S_0 is budget-feasible and sw(S_0, v⃗) ≥ sw(S* ∩ S_0, v⃗)
-- statement:
--   Let $m=2^K$ be the number of alternatives, $\vec v$ a normalized utility profile, $S_0=\{a: 0\le c_a\le 1/m^2\}$ the cheapest cost bucket, and $S^*$ a welfare-maximizing set in $\mathcal F_c$. Then
--   $$
--   c(S_0)\le 1\qquad\text{and}\qquad \mathrm{sw}(S_0,\vec v)\ \ge\ \mathrm{sw}(S^*\cap S_0,\vec v).
--   $$
--   Mechanism B, which funds all of $S_0$, therefore covers the part of the optimum lying in the cheapest bucket.
--
--   **Formalization Note.** $m$ is `Fintype.card A` $=2^K$. `IsWelfareOptimal` pins $S^*$ to the page's optimum.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), proof of Theorem 3.5, Mechanism B, p. 14

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem mechanism_B {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (v : Fin n → A → ℝ) (hv : IsUtilityProfile v) (m K : ℕ) (hA : Fintype.card A = m)
    (hmK : m = 2 ^ K) (Sstar : Finset A) (hS : IsWelfareOptimal c v Sstar) :
    cost c (bucket c m 0) ≤ 1 ∧ sw v (Sstar ∩ bucket c m 0) ≤ sw v (bucket c m 0) := by sorry

end PBElicit.RandThresh
