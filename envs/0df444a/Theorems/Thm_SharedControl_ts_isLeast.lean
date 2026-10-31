-- Prove2me | Theorems.Thm_SharedControl_ts_isLeast
-- name    : SharedControl.ts_isLeast
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:07:42.342367+00:00
-- url     : https://prove2.me/theorems/e0c68fc9-660d-49ec-9add-103362ed6d46
-- title:
--   §2.1, p.4 — $t_s$ is the least transfer satisfying (1), and (1) binds at $t_s$ unless $t_s = 0$
-- statement:
--   Assume the standing assumptions. Let $t_s$ be the infimum of the nonnegative transfers $t$ satisfying Inequality (1),
--
--   $$
--   E[s_g + t \mid m_g \ge t] \ge 0 .
--   $$
--
--   Then $t_s$ itself satisfies (1), so it is the smallest such transfer, and
--
--   $$
--   t_s = 0 \quad\text{or}\quad E[s_g + t_s \mid m_g \ge t_s] = 0 .
--   $$
--
--   This makes the paper's "let $t_s$ be the smallest nonnegative transfer that satisfies Inequality (1)" well defined, and it is the dichotomy the paper derives from the continuity of the left-hand side of (1) in $t$.
--
--   Differences from the source:
--   - reading: either E[sg + ts | mg ≥ t] = 0 or ts = 0, with t in the conditioning event → either ts = 0 or E[sg + ts | mg ≥ ts] = 0; reason: ts is the only transfer of the sentence, so the event is read as mg ≥ ts
--   - encoding: E[sg + t | mg ≥ t] in Inequality (1) → the integral of πg − r + t against the conditional measure P[|{mg ≥ t}], with Pr[mg ≥ t] > 0 required for t to satisfy (1); reason: a conditional expectation given a null event is undefined (Lean's cond returns the zero measure there); the least transfer satisfying (1) is unchanged
--   - generalization: r has a continuous distribution with support on [rl, rh], rl the minimum of the support → the law of r is atomless, r ∈ [rl, rh] almost surely, and every set {r < rl + ε}, {rh − ε < r} (ε > 0) has positive probability; reason: these three properties follow from supp(law r) = [rl, rh]; gaps inside (rl, rh) are also allowed, and no density is assumed, so the source's models are a special case
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §2.1, p.4

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Standing
import Definitions.Def_SharedControl_Feasible
import Definitions.Def_SharedControl_ts

open MeasureTheory ProbabilityTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §2.1, p.4 (PDF p.5): "Thus, let ts be the smallest
nonnegative transfer that satisfies Inequality (1). Because r has a continuous distribution and
bounded support, the left-hand side of (1) is continuous and unbounded in t. Hence, either
E[sg + ts | mg ≥ t] = 0 or ts = 0."

Under the standing assumptions, the set of nonnegative transfers satisfying (1) has a least
element, and that element is `ts` (so "the smallest" is well defined), and either `ts = 0` or (1)
holds with equality at `ts`: `E[πg − r + ts | πg + r ≥ ts] = 0`.

**Formalization Note.** The page's "E[sg + ts | mg ≥ t] = 0" has `t` in the conditioning
event; it is read as `mg ≥ ts` (the only transfer in the sentence is `ts`). Conditional
expectation is the integral against `P[|{mg ≥ ts}]` (`ProbabilityTheory.cond`); see
`SharedControl.Feasible` for the positivity of the conditioning probability. -/
theorem ts_isLeast {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : Standing M) :
    IsLeast {t | Feasible M t} (ts M) ∧
      (ts M = 0 ∨
        ∫ ω, (M.πg - M.r ω + ts M) ∂(M.P[|{ω | ts M ≤ M.πg + M.r ω}]) = 0) := by sorry

end SharedControl
