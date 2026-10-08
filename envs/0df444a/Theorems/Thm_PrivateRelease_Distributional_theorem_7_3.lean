-- Prove2me | Theorems.Thm_PrivateRelease_Distributional_theorem_7_3
-- name    : PrivateRelease.Distributional.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:44.457001+00:00
-- url     : https://prove2.me/theorems/512b1259-2414-41a7-a390-c2577c17f669
-- title:
--   Theorem 7.3 — (ε, β)-distributional privacy with β = o(1/n²) implies ε-differential privacy
-- statement:
--   Let $X$ be a data universe and $R$ a measurable space. For each database size $n\in\mathbb N$ let $A_n$ be a mechanism mapping each database $D\subseteq X$ of size $n$ to the law $A_n(D)$ of its output on $R$, let $\varepsilon\in\mathbb R$, and let $(\beta_n)_{n}$ be real numbers with $\beta_n=o(1/n^2)$, that is,
--   $$n^2\beta_n\longrightarrow0\qquad(n\to\infty).$$
--   If $A_n$ is $(\varepsilon,\beta_n)$-distributionally private on databases of size $n$ for every $n$, then for all sufficiently large $n$ the mechanism $A_n$ is $\varepsilon$-differentially private on databases of size $n$: for all neighbouring $D,D'$ of size $n$ and every measurable event $E\subseteq R$,
--   $$\Pr[A_n(D)\in E]\le e^{\varepsilon}\Pr[A_n(D')\in E].$$
--
--   This is the paper's statement that distributional privacy, with failure probability small compared to $1/n^2$, is at least as strong as differential privacy.
--
--   **Formalization Note.** "$\beta=o(1/n^2)$" is an asymptotic condition, so the theorem is stated for a family $(A_n,\beta_n)_n$ indexed by the database size; a single mechanism $A$ on all finite sets is the case $A_n=A$. The conclusion is "for all sufficiently large $n$" (`∀ᶠ n in atTop`): for a fixed small $n$, $\beta_n$ may exceed $1/(n+1)^2$ and the implication then fails. Databases are sets, neighbours differ by replacing one element, and events are measurable sets; see the definition item.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 19, Theorem 7.3

import Mathlib
import Definitions.Def_PrivateRelease_Distributional_Privacy

namespace PrivateRelease.Distributional

open MeasureTheory Filter Topology

/-- Theorem 7.3 (p. 19): if, for every database size `n`, the mechanism `A n` is
(ε, βₙ)-distributionally private with `βₙ = o(1/n²)`, i.e. `n² βₙ → 0`, then `A n` is
ε-differentially private for all sufficiently large `n`. -/
theorem theorem_7_3 {X R : Type} [DecidableEq X] [MeasurableSpace R] (A : ℕ → Finset X → Measure R)
    (β : ℕ → ℝ) (ε : ℝ) (hβ : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * β n) atTop (𝓝 0))
    (hA : ∀ n, IsDistPrivate (A n) n ε (β n)) :
    ∀ᶠ n in atTop, IsDPSet (A n) n ε := by sorry

end PrivateRelease.Distributional
