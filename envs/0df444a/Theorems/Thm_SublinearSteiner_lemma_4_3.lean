-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_4_3
-- name    : SublinearSteiner.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:50.232889+00:00
-- url     : https://prove2.me/theorems/adbb3a98-f286-4f2c-b1d3-a54776da1b18
-- title:
--   Lemma 4.3 — call bound for local random-greedy matching
-- statement:
--   Let $H$ be a finite loopless multigraph on $U$ with $m=|U|\ge1$ and $p$ labeled edge copies, and $N_H=m+p+2$. Fix a directed copy $(e,u)$, and let $Q(e,u)$ be the number of invocations of $\mathrm{EO}(e,u)$, cached ones included, summed over separate calls $\mathrm{VO}(v)$ for all $v\in U$. Over a uniformly random order,
--   $$\mathbb E\,Q(e,u)=O(\log N_H).$$
--   Consequently, for a uniformly random root independent of the order, the expected number of oracle invocations is $O((1+p/m)\log N_H)$, and the expected number of invocations at a fixed vertex $x$ is $O((1+d_x)\log N_H/m)$, where $d_x$ is its degree.
--
--   The bound has no dependence on the maximum degree, which is what makes the local oracle cheap on the dense port multigraph.
--
--   Differences from the source:
--   - reading: oracle invocations, and invocations at x → EO calls plus the root call VO(v); at x, the calls EO(·, x) plus the root call VO(x); reason: the strong count; the factor 1 + d_x pays for it
--   - encoding: O(·) → one constant C chosen before H; reason: the O of the page is universal
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.3, p.21

import Mathlib
import Definitions.Def_SublinearSteiner_Multigraph

namespace SublinearSteiner

open Multigraph in
/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.3 (Call bound), p.21. Fix `H` and a directed copy `(e, u)`, and let `Q(e, u)` be the number of invocations
of `EO(e, u)`, cached ones included, summed over separate calls `VO(v)` for all `v ∈ U`. Over a uniformly random order,
`E Q(e, u) = O(log N_H)`. Consequently, for a uniformly random root independent of the order, the expected number of oracle
invocations is `O((1 + p/m) log N_H)`, and the expected number of invocations at a fixed vertex `x` is
`O((1 + d_x) log N_H/m)`, where `d_x` is its degree.

**Formalization Note.** The constant `C` is universal, chosen before `H`. `m = |U| ≥ 1`, `p = |E|`, `N_H = m + p + 2`. The
invocations of one call count `EO` calls plus the root call `VO(v)`. Invocations at `x` count `EO(·, x)` plus the root call
`VO(x)`, which is what the factor `1 + d_x` pays for. -/
theorem lemma_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (U E : Type) [Fintype U] [Nonempty U] [DecidableEq U] [Fintype E] [DecidableEq E]
      (H : Multigraph U E),
      let m : ℝ := Fintype.card U
      let p : ℝ := Fintype.card E
      let NH : ℝ := m + p + 2
      (∀ (e : E) (u : U), H.Incident e u →
        avgOrder (fun π => ∑ v : U, (((vo H π v).2.count (e, u) : ℕ) : ℝ)) ≤ C * Real.log NH) ∧
      avgOrder (fun π => m⁻¹ * ∑ v : U, (1 + ∑ q : E × U, (((vo H π v).2.count q : ℕ) : ℝ)))
        ≤ C * (1 + p / m) * Real.log NH ∧
      (∀ x : U,
        avgOrder (fun π => m⁻¹ * ∑ v : U,
            ((if v = x then (1 : ℝ) else 0) + ∑ e : E, (((vo H π v).2.count (e, x) : ℕ) : ℝ)))
          ≤ C * (1 + ((Finset.univ.filter fun e => H.Incident e x).card : ℝ)) * Real.log NH / m) := by sorry

end SublinearSteiner
