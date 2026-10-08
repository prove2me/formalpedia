-- Prove2me | Theorems.Thm_WhittleGittins_Retirement_lemma1_monotone_convex
-- name    : WhittleGittins.Retirement.lemma1_monotone_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:28.820757+00:00
-- url     : https://prove2.me/theorems/ccc7f897-0d6a-405c-b09c-f3a2bb83681c
-- title:
--   Lemma 1 — F(x, M) is non-decreasing and convex in M, equal to Φ(x) for M ≤ k and to M for M ≥ K
-- statement:
--   Consider Whittle's $N$-project bandit process ($N \ge 1$) with rewards bounded as in (1), $k(1-\beta)\le R_i(x_i)\le K(1-\beta)$, and discount $0\le\beta<1$. Let $\Phi$ be the value of the continuing process, the bounded solution of $\Phi = \max_i L_i\Phi$ (2), and let $F(x, M)$ be the value of the $M$-process, in which one may also retire at any time for the reward $M$: for each $M$, $F(\cdot, M)$ is the bounded solution of $F = \max(M, \max_i L_i F)$ (4).
--
--   Then for every state $x$, $F(x, M)$ is a non-decreasing convex function of $M$ with
--   $$F(x, M) = \begin{cases}\Phi(x), & M \le k,\\ M, & M \ge K.\end{cases} \qquad (5)$$
--   Moreover, for $M < k$ the optimal policies of the $M$-process and the continuing process are identical: retirement is never optimal ($F(x, M) > M$), and every project has the same one-step value in both processes, $L_iF(\cdot, M)(x) = L_i\Phi(x)$.
--
--   Lemma 1 says that the $M$-process interpolates between the continuing process (small $M$) and immediate retirement (large $M$); its convexity is what makes $\partial F/\partial M$ meaningful in the identity (12).
--
--   **Formalization Note** $\Phi$ and $F$ are taken as any bounded measurable solutions of (2) and (4) (`IsContinuingValue`, `IsMProcessValue`). Projects are indexed by `Fin N` with `[NeZero N]`. The last sentence of the Lemma, which speaks of optimal policies, is rendered without a policy layer: for $M < k$, retirement is strictly worse than continuing and the maximised quantities $L_i F(\cdot,M)(x)$ and $L_i\Phi(x)$ coincide for every $i$, so the same projects are optimal in both processes.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), p. 144 (PDF 2), Lemma 1, (5)

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Lemma 1 (p. 144): `F(x, M)` is non-decreasing and convex in `M`, equals `Φ(x)` for `M ≤ k` and
`M` for `M ≥ K`; for `M < k` retirement is never optimal and the one-step values `Lᵢ F` and
`Lᵢ Φ` coincide, so the optimal policies of the two processes are identical. -/
theorem lemma1_monotone_convex {N : ℕ} [NeZero N] {X : Fin N → Type*}
    [∀ i, MeasurableSpace (X i)] (B : BanditProcess N X)
    (F : (∀ j, X j) → ℝ → ℝ) (Φ : (∀ j, X j) → ℝ)
    (hF : IsMProcessValue B F) (hΦ : IsContinuingValue B Φ) (x : ∀ j, X j) :
    Monotone (F x) ∧ ConvexOn ℝ Set.univ (F x) ∧
      (∀ M, M ≤ B.k → F x M = Φ x) ∧ (∀ M, B.K ≤ M → F x M = M) ∧
      (∀ M, M < B.k → M < F x M ∧ ∀ i, Lop B i (fun z => F z M) x = Lop B i Φ x) := by sorry

end WhittleGittins.Retirement
