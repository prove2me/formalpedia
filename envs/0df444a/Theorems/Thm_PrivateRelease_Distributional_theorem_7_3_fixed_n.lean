-- Prove2me | Theorems.Thm_PrivateRelease_Distributional_theorem_7_3_fixed_n
-- name    : PrivateRelease.Distributional.theorem_7_3_fixed_n
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:21.076372+00:00
-- url     : https://prove2.me/theorems/0be8e488-cd9a-4b89-90ba-5613fe2da67d
-- title:
--   Theorem 7.3, fixed-n form — (ε, β)-distributional privacy with β < 1/(n+1)² implies ε-differential privacy
-- statement:
--   Let $X$ be a data universe, $R$ a measurable space, $n\in\mathbb N$, and let $A$ be a mechanism that maps each database $D\subseteq X$ of size $n$ to the law $A(D)$ of its output on $R$. Let $\varepsilon,\beta\in\mathbb R$ with
--   $$\beta<\frac{1}{(n+1)^2}.$$
--   If $A$ is $(\varepsilon,\beta)$-distributionally private on databases of size $n$, then $A$ is $\varepsilon$-differentially private on databases of size $n$: for all neighbouring $D,D'$ (of size $n$, differing in one element) and every measurable event $E\subseteq R$,
--   $$\Pr[A(D)\in E]\le e^{\varepsilon}\Pr[A(D')\in E].$$
--
--   This is the argument of the proof of Theorem 7.3 for a single database size: the population $S=D\cup D'$ has $n+1$ elements, and each ordered pair of its $n$-subsets carries probability $1/(n+1)^2$, so a failure probability below that threshold forces every pair to be good.
--
--   **Formalization Note.** The paper writes "with probability $2/n^2$ we have $\{D_1',D_2'\}=\{D_1,D_2\}$", the probability of the unordered pair, approximating $2/(n+1)^2$ by $2/n^2$. The definition counts ordered pairs, each of which has probability exactly $1/(n+1)^2$; this is the threshold the argument proves. At $n=0$ no pair of neighbours exists and the conclusion holds trivially.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 19, proof of Theorem 7.3

import Mathlib
import Definitions.Def_PrivateRelease_Distributional_Privacy

namespace PrivateRelease.Distributional

open MeasureTheory

/-- Theorem 7.3, fixed-`n` form (proof of Theorem 7.3, p. 19): if the mechanism `A` on
set-databases of size `n` is (ε, β)-distributionally private with `β < 1/(n+1)²`, then it is
ε-differentially private on set-databases of size `n`. -/
theorem theorem_7_3_fixed_n {X R : Type} [DecidableEq X] [MeasurableSpace R] (A : Finset X → Measure R)
    (n : ℕ) (ε β : ℝ) (hβ : β < 1 / ((n : ℝ) + 1) ^ 2) (hA : IsDistPrivate A n ε β) :
    IsDPSet A n ε := by sorry

end PrivateRelease.Distributional
