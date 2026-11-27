-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_A_21
-- name    : SampleMechDesign.Supplement.theorem_A_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:54:45.694713+00:00
-- url     : https://prove2.me/theorems/9c96303f-4b3d-429c-83ed-c597363845fc
-- title:
--   Theorem A.21 (corrected: typo $V\to H$) — $2^m-2$ two-bidder additive valuations that VVCAs separate: profit $0$ on $H$, $1-\beta$ off $H$
-- statement:
--   For any $m\ge2$ and any $\beta\in(0,1)$ there is a set of $N=2^m-2$ distinct 2-bidder additive valuation vectors $V=\{v^1,\dots,v^N\}$ such that for any $H\subseteq V$ there is a VVCA with
--   $$
--   \mathrm{profit}(v^i)=0\ \text{ if } v^i\in H,\qquad \mathrm{profit}(v^i)=1-\beta\ \text{ if } v^i\notin H .
--   $$
--   The paper prints "if $v^i\in V$" and "if $v^i\notin V$", which is contradictory because every $v^i$ lies in $V$; the claim in its proof reads $H$. Lemmas A.22–A.23 put the profit $1-\beta$ on $H$ and $0$ off $H$; since $H$ ranges over all subsets, the two assignments give the same theorem. The cost is zero and the statement holds for every tie-breaking rule.
--
--   This separation property gives the sample-complexity lower bound $2^m-2$ for VVCAs (Theorem A.16).
--
--   Differences from the source:
--   - correction: profit 0 on vⁱ if vⁱ ∈ V and profit 1 − β on vⁱ if vⁱ ∉ V → profit 0 on vⁱ if vⁱ ∈ H and profit 1 − β on vⁱ if vⁱ ∉ H; reason: typo: as printed the statement is contradictory (every vⁱ ∈ V); the proof's claim on p.37 reads H
--   - reading: the cost function and the tie-breaking rule is not specified → zero cost; every tie-breaking rule; reason: the construction omits the cost; ties are left open by the paper
--   - encoding: a set V of N valuation functions and subsets H ⊆ V → an injective N-tuple V and sets H of its indices; reason: same instances
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem A.21, p.37 (PDF p.37); Lemmas A.22–A.23, p.37

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_vvcaBoost

namespace SampleMechDesign.Supplement

/-- **Theorem A.21, typo corrected.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.37. For
any `m ≥ 2` and any `β ∈ (0, 1)` there is a set of `N = 2^m − 2` distinct 2-bidder additive
valuation vectors `V = {v^1, …, v^N}` such that for any `H ⊆ V` there is a VVCA with profit `0` on
`v^i` if `v^i ∈ H` and profit `1 − β` on `v^i` if `v^i ∉ H`.

**Formalization Note.**
* Typo: the paper prints "if `v^i ∈ V`" and "if `v^i ∉ V`", which is contradictory since every
  `v^i ∈ V`; the proof's claim on p.37 reads `H`. (Lemmas A.22–A.23 put profit `1 − β` on `H` and
  `0` off `H`; since `H` ranges over all subsets, the two assignments are the same theorem.)
* A VVCA is an AMA (`w > 0`, `λ ≥ 0`) with boost `λ(Q) = ∑_j c_{j, q_j}`. Zero cost, as in the
  construction. The profit `1 − β` is exact. The statement holds for every tie-breaking rule. -/
theorem theorem_A_21 {m : ℕ} (hm : 2 ≤ m) (tb : BVal 2 m → Finset (Alloc 2 m) → Alloc 2 m)
    (htb : IsChoice tb) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ V : Fin (2 ^ m - 2) → AVal 2 m, Function.Injective V ∧
      ∀ H : Set (Fin (2 ^ m - 2)), ∃ (w : Fin 2 → ℝ) (cc : Fin 2 → Finset (Fin m) → ℝ),
        IsAMAParam w (vvcaBoost cc) ∧
        ∀ i, (i ∈ H → amaProfit (fun _ => 0) tb w (vvcaBoost cc) (additiveVal (V i)) = 0) ∧
          (i ∉ H → amaProfit (fun _ => 0) tb w (vvcaBoost cc) (additiveVal (V i)) = 1 - β) := by sorry

end SampleMechDesign.Supplement
