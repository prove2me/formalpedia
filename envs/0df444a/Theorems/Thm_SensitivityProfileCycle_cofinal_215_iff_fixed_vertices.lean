-- Prove2me | Theorems.Thm_SensitivityProfileCycle_cofinal_215_iff_fixed_vertices
-- name    : SensitivityProfileCycle.cofinal_215_iff_fixed_vertices
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-24T09:20:07.13682+00:00
-- url     : https://prove2.me/theorems/fb05e74d-6d1c-4e5d-a7c6-078e11b68921
-- title:
--   Approaching exponent 2.15 with profile cycles is equivalent to approaching it at a single vertex count
-- statement:
--   Write $Q_k(C)$ for $R>1$ and $R^{43k+42}\le(K^L)^{20(k+1)}$, where $R,K,L$ are the radius, vertex count, and period of a profile cycle $C$. The following assertions are equivalent.
--
--   1. For every $k\ge0$ there is a profile cycle satisfying $Q_k$.
--   2. There is one integer $K$ with $85\le K\le12407$ such that, for every $k\ge0$, some profile cycle on exactly $K$ vertices satisfies $Q_k$.
--
--   The tournament, labels, number of states, period, and profiles may vary with $k$.
-- source:
--   New reduction of the exact outstanding sufficient condition https://prove2.me/theorems/4d1841a1-42e4-425c-be39-0fbb8a5cd5af . It uses the return-factor bound https://prove2.me/theorems/3559fa37-235a-4ae9-92fc-f97a9861b5b3 and the integer interval calculation from the corresponding single-cycle result https://prove2.me/theorems/8592e3c4-dd97-4425-a406-e02b0fedddd8 .

import Definitions.Def_SensitivityProfileCycle

theorem SensitivityProfileCycle.cofinal_215_iff_fixed_vertices :
    (∀ k : ℕ, ∃ C : SensitivityProfileCycle.Certificate,
      1 < C.radius ∧ C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1))) ↔
    ∃ K : ℕ, 85 ≤ K ∧ K ≤ 12407 ∧ ∀ k : ℕ, ∃ C : SensitivityProfileCycle.Certificate,
      C.vertices = K ∧ 1 < C.radius ∧ C.radius^(43*k+42) ≤ (C.vertices^C.period)^(20*(k+1)) := by sorry
