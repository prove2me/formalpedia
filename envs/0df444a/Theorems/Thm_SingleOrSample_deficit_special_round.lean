-- Prove2me | Theorems.Thm_SingleOrSample_deficit_special_round
-- name    : SingleOrSample.deficit_special_round
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:35.336909+00:00
-- url     : https://prove2.me/theorems/6c88ba0d-338e-4d6a-b938-86d81772f38b
-- title:
--   §4.2.2 — a special round does not raise the deficit
-- statement:
--   Let $P$ be a labelling of the goods into $n$ bundles and $w\ge0$ weights with $\sum_{e\in P_h}w_e=1$ for every $h$, and let the arbitrary choice $ch$ select an active bundle whenever one exists. Then:
--
--   1. initially $W_0=N_0=n$ and $D_0=0$;
--   2. $|\mathcal B_j|=n-t_j$ whenever $t_j\le n$;
--   3. a non-special round leaves the active collection unchanged;
--   4. in a special round selecting $e$ with some active bundle, the deactivated bundle $d$ is the bundle of $e$ if that is active and the arbitrary choice $ch$ otherwise; $d$ is active, its surviving weight $b$ satisfies $b\le1$, the round changes $N_j$ to $N_j-1$ and $W_j$ to $W_j-b$, and so $D_{j+1}=D_j-(1-b)$;
--   5. consequently $D_{j+1}\le D_j$ in every special round.
--
--   The deficit is therefore raised only by non-special rounds, which is what makes a bound in terms of the number of non-special rounds possible.
--
--   Differences from the source:
--   - generalization: supporting prices of an MMS-defining partition → any weights w ≥ 0 with bundle sums 1; reason: the page's argument uses only these two properties
--   - generalization: j ∈ {0,…,i−1} → every history, also when no bundle is active (where the deficit does not change); reason: the page's range has t_j < n; the extra case is a one-line check
--   - encoding: an arbitrary currently active bundle → a function ch of the history before the round; reason: the choice is arbitrary and may depend on the history, so this covers every choice rule
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §4.2.2, eq. (5), p.15

import Mathlib
import Definitions.Def_SingleOrSample_chainPrice
import Definitions.Def_SingleOrSample_deficit

namespace SingleOrSample

/-- **A special round does not raise the deficit** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §4.2.2, p.15). For weights `w ≥ 0` with bundle
sums `1`: `W_0 = N_0 = n` and `D_0 = 0`; `|B_j| = n − t_j` while `t_j ≤ n`; a non-special round leaves the
active collection unchanged; and in a special round selecting `e`, the deactivated bundle `d` is the
bundle of `e` if that is active and `ch` of the history otherwise, it is active, its surviving weight `b`
is at most `1`, the round changes `N_j` to `N_j − 1` and `W_j` to `W_j − b`, so
`D_{j+1} = D_j − (1 − b) ≤ D_j`.

**Formalization Note.** The weights are any nonnegative weights with bundle sums `1`, which is more
general than supporting prices and is all the page uses. `ch` is the page's arbitrary choice of an active
bundle. When no bundle is active (`t_j ≥ n`), a special round leaves the deficit unchanged. -/
theorem deficit_special_round {m n : ℕ} (P : Fin m → Fin n) (w : Fin m → ℝ) (hw0 : ∀ e, 0 ≤ w e)
    (hw1 : ∀ b, ∑ e ∈ bundle P b, w e = 1) (ch : Hist m → Fin n)
    (hch : ∀ h, (activeBundles P ch h).Nonempty → ch h ∈ activeBundles P ch h) :
    survivingWeight P w ch [] = n ∧ (activeBundles P ch []).card = n ∧ deficit P w ch [] = 0 ∧
    (∀ h, specialCount h ≤ n → (activeBundles P ch h).card = n - specialCount h) ∧
    (∀ h picks, activeBundles P ch (h ++ [.sampled picks]) = activeBundles P ch h) ∧
    (∀ h e, (activeBundles P ch h).Nonempty →
      let d : Fin n := if P e ∈ activeBundles P ch h then P e else ch h
      let b : ℝ := ∑ e' ∈ (remaining h).filter (fun e' => P e' = d), w e'
      d ∈ activeBundles P ch h ∧ b ≤ 1 ∧
      activeBundles P ch (h ++ [.special e]) = (activeBundles P ch h).erase d ∧
      ((activeBundles P ch (h ++ [.special e])).card : ℝ) = (activeBundles P ch h).card - 1 ∧
      survivingWeight P w ch (h ++ [.special e]) = survivingWeight P w ch h - b ∧
      deficit P w ch (h ++ [.special e]) = deficit P w ch h - (1 - b)) ∧
    (∀ h e, deficit P w ch (h ++ [.special e]) ≤ deficit P w ch h) := by sorry

end SingleOrSample
