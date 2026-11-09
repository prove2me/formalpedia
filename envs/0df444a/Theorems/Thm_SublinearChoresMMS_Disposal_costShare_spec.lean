-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_costShare_spec
-- name    : SublinearChoresMMS.Disposal.costShare_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:30:23.493168+00:00
-- url     : https://prove2.me/theorems/900eb1c5-6c46-4b65-87d6-a7b927bb61bc
-- title:
--   Section 2 — the attained cost minimax share
-- statement:
--   For a finite real singleton-cost vector $u$ and any positive integer $d$, the reused functional is exactly the cost minimax:
--
--   $$\mu^d=\min_{A:M\to[d]}\max_{j\in[d]}\sum_{e:A(e)=j}u(e).$$
--
--   Some complete labelled partition has every part cost at most $\mu^d$, and every complete labelled partition has a part cost at least $\mu^d$. Thus both finite extrema are genuine and the minimum is attained, including when $M$ is empty.
--
--   This helper exposes the sign-conversion interface used by the mission; it is a separate proof target, not an assumed optimum.
--
--   Differences from the source:
--   - generalization: nonnegative singleton costs → arbitrary real singleton costs in this finite-extremum helper; reason: sign reversal of finite maxima and minima and their attainment do not require nonnegativity; the nonnegative source specializes immediately
--   - encoding: cost minimax share over labelled partitions → the negative of LittleCharity.MMS.mms evaluated at negative additive bundle costs; reason: negation exchanges finite maxima and minima; no goods nonnegativity predicate is imposed, and costShare_spec states the attained minimax characterization
--   - encoding: finite agents, chores, complete partitions and finite lotteries → agents Fin n, chores Fin m, allocation maps and normalized finite lists with real weights; reason: bijections identify the same finite instances and partitions; repeated lottery atoms may be merged and positive weights define support
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), §2, printed p. 4 / PDF p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Setting

noncomputable section

namespace SublinearChoresMMS.Disposal

/-- Section 2, printed p. 4 / PDF p. 5: sign conversion to the attained finite minimax.
This interface does not impose the published goods nonnegativity predicate. -/
theorem costShare_spec {m d : ℕ} (hd : 0 < d) (u : Fin m → ℝ) :
    costShare u d = ⨅ A : Fin m → Fin d, ⨆ j : Fin d,
      (∑ e ∈ Finset.univ.filter (fun e => A e = j), u e) ∧
    (∃ A : Fin m → Fin d, ∀ j, (∑ e ∈ Finset.univ.filter (fun e => A e = j), u e) ≤ costShare u d) ∧
    ∀ A : Fin m → Fin d, ∃ j, costShare u d ≤
      ∑ e ∈ Finset.univ.filter (fun e => A e = j), u e := by sorry

end SublinearChoresMMS.Disposal
