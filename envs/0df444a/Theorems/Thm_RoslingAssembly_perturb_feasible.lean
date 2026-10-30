-- Prove2me | Theorems.Thm_RoslingAssembly_perturb_feasible
-- name    : RoslingAssembly.perturb_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:48:12.278985+00:00
-- url     : https://prove2.me/theorems/f784165c-09a8-409f-a5c3-6323e56c969e
-- title:
--   The perturbed policy is feasible
-- statement:
--   Let $\pi$ be a non-anticipating measurable policy satisfying constraint (3) along every demand path. For every item $i$ and every $n\ge0$, the policy that orders $n$ more units of every $k\in\{i\}\cup B(i)$ in period $M_m-M_k+1$, where $M_m=\max_{k\in\{i\}\cup B(i)}M_k$, and holds them forever, is again a non-anticipating measurable policy satisfying (3) along every demand path.
--
--   The staggering by total lead times makes the extra components arrive exactly when the next assembly stage needs them.
--
--   **Formalization Note** No assumption on the history or the demand law is needed.
--
--   Differences from the source:
--   - generalization: one more unit → n ≥ 0 more units, any real n ≥ 0; reason: n = 1 is the paper's policy
--   - generalization: the standing assumptions of problem P (demand law, history) → no assumption on the demand law or the history; reason: feasibility of the perturbation holds pathwise for every feasible base policy
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix B, Proof of Theorem 4, p. 578 (unnumbered)

import Mathlib
import Definitions.Def_RoslingAssembly_IsPolicy
import Definitions.Def_RoslingAssembly_Feasible
import Definitions.Def_RoslingAssembly_perturb

namespace RoslingAssembly

/-- **The perturbed policy is feasible** (Appendix B, Proof of Theorem 4, p. 578, unnumbered).
Rosling, *Optimal Inventory Policies for Assembly Systems under Random Demands*, Operations
Research 37(4), 1989, p. 578: "Then consider an alternative policy that orders one more unit in
period 1 of the component, m, with the greatest total lead-time M_m, in period M_m − M_l + 1 of
the component, l, with the next to the greatest total lead-time and so on, so that one more unit
is ordered of item i in period M_m − M_i + 1. This additional unit is held in stock forever."

If `pol` is a non-anticipating measurable policy satisfying (3) on every demand path, then for
every item `i` and every `n ≥ 0` the policy that adds `n` units of every `k ∈ {i} ∪ B(i)` from
period `M_m − M_k + 1` on (`perturb`) is again a non-anticipating measurable policy satisfying
(3) on every demand path.

**Formalization Note.** No assumption on the history or on the demand law is needed. Lean
decision index `t` is paper period `t + 1`. Items are `Fin N`, 0-based. -/
theorem perturb_feasible {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (Yh : ℤ → Fin N → ℝ)
    (ξh : ℤ → ℝ) (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (hpol : IsPolicy pol)
    (hfeas : Feasible net ℓ Yh ξh pol) (i : Fin N) (n : ℝ) (hn : 0 ≤ n) :
    IsPolicy (perturb net ℓ pol i n) ∧ Feasible net ℓ Yh ξh (perturb net ℓ pol i n) := by sorry

end RoslingAssembly
