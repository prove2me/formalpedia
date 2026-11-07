-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_1
-- name    : SmoothedNash.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:10.461299+00:00
-- url     : https://prove2.me/theorems/42fb7401-c504-4ec7-9c25-3e4e8cf97b5a
-- title:
--   Lemma 2.1 — fixed grid refinement: $\rho_t$-net, $|N_t(A)| \le C^{mn}2^{tR}$, $\le 2^R$ children, unique parents
-- statement:
--   Fix a support profile $A = (A_1, \dots, A_m)$ with $R = \sum_i (|A_i| - 1)$. Let $q_0 = \max\{1, \lceil R/m \rceil\}$, $q_t = 2^t q_0$, and
--   $$
--   N_t(A) := \{x \in K_A : q_t x_i(a) \in \mathbb Z_{\ge 0} \text{ for all } i \in [m],\ a \in A_i\}.
--   $$
--   There is a universal constant $C > 1$ such that for every $m$, $n$, every support profile $A$ and every $t \ge 0$:
--   0. the numerator vectors of the level-$t$ grid correspond bijectively, through $k \mapsto k/q_t$, to the points of $N_t(A)$;
--   1. $N_t(A)$ is a $\rho_t$-net of $K_A$: every $x \in K_A$ has a grid point $c \in N_t(A)$ with $\|x - c\|_1 \le \rho_t$;
--   2. $|N_t(A)| \le C^{mn} 2^{tR}$;
--   3. each point $c \in N_t(A)$ has at most $2^R$ children, and each child lies in $B_A(c, \rho_t)$;
--   4. every point of $N_{t+1}(A)$ is a child of exactly one point of $N_t(A)$ (its unique parent).
--
--   The grids are fixed in advance and nested through the children relation; this is what lets Algorithm 2 refine a surviving center locally without generating any point twice.
--
--   Differences from the source:
--   - encoding: N_t(A) as a set of profiles → the numerator set grid A t with gridPt A t k = k / q_t; reason: clause 0 states that gridPt A t maps grid A t bijectively onto the paper's N_t(A)
--   - encoding: q_0 = max{1, ⌈R/m⌉} → max 1 ((R + m − 1) / m) in ℕ; reason: equal to ⌈R/m⌉ for m ≥ 1, and both are 0 when m = 0 (then R = 0)
--   - generalization: a game with m players, each with n actions (m, n ≥ 1 implicit) → any m, n ∈ ℕ, including 0; reason: the statement specializes to m, n ≥ 1; for m = 0 or n = 0 the instance is degenerate (the hypotheses are unsatisfiable or the claim is immediate)
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14 (proof p.20)

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_R
import Definitions.Def_SmoothedNash_InK
import Definitions.Def_SmoothedNash_l1
import Definitions.Def_SmoothedNash_rho
import Definitions.Def_SmoothedNash_q
import Definitions.Def_SmoothedNash_grid
import Definitions.Def_SmoothedNash_gridPt
import Definitions.Def_SmoothedNash_children

namespace SmoothedNash

/-- **Lemma 2.1 (Fixed grid refinement)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.14). Let `q_0 = max{1, ⌈R/m⌉}`, `q_t = 2^t q_0`
and `N_t(A) := {x ∈ K_A : q_t x_i(a) ∈ ℤ_{≥0}}`. For every `t ≥ 0`, `N_t(A)` is a `ρ_t`-net of
`K_A` with `|N_t(A)| ≤ C^{mn} 2^{tR}`; each point has at most `2^R` children, each child lies in
`B_A(c, ρ_t)`, and every point of `N_{t+1}(A)` has a unique parent in `N_t(A)`.

The conjunction states:
0. `gridPt A t` maps the numerator set `grid A t` injectively onto the paper's `N_t(A)`;
1. the `ρ_t`-net property;
2. the cardinality bound, with one universal `C > 1` for all `m, n, A, t`;
3. at most `2^R` children, each within `ρ_t` of its parent;
4. every point of `N_{t+1}(A)` is a child of exactly one point of `N_t(A)`. -/
theorem lemma_2_1 :
    (∀ {m n : ℕ} (A : SupportProfile m n) (t : ℕ),
      Set.InjOn (gridPt A t) ↑(grid A t) ∧
      gridPt A t '' ↑(grid A t) =
        {x | InK A x ∧ ∀ i, ∀ a ∈ A.1 i, ∃ z : ℕ, (q A t : ℝ) * x i a = z}) ∧
    (∀ {m n : ℕ} (A : SupportProfile m n) (t : ℕ) (x : Fin m → Fin n → ℝ), InK A x →
      ∃ k ∈ grid A t, l1 x (gridPt A t k) ≤ rho m t) ∧
    (∃ C : ℝ, 1 < C ∧ ∀ {m n : ℕ} (A : SupportProfile m n) (t : ℕ),
      ((grid A t).card : ℝ) ≤ C ^ (m * n) * 2 ^ (t * R A)) ∧
    (∀ {m n : ℕ} (A : SupportProfile m n) (t : ℕ) (k : Fin m → Fin n → ℕ), k ∈ grid A t →
      (children A t k).card ≤ 2 ^ R A ∧
      ∀ k' ∈ children A t k, l1 (gridPt A (t + 1) k') (gridPt A t k) ≤ rho m t) ∧
    (∀ {m n : ℕ} (A : SupportProfile m n) (t : ℕ) (k' : Fin m → Fin n → ℕ), k' ∈ grid A (t + 1) →
      ∃! k, k ∈ grid A t ∧ k' ∈ children A t k) := by sorry

end SmoothedNash
