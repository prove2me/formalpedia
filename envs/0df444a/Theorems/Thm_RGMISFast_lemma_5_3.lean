-- Prove2me | Theorems.Thm_RGMISFast_lemma_5_3
-- name    : RGMISFast.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:06.27793+00:00
-- url     : https://prove2.me/theorems/29f73e9a-c847-473f-abcb-28bbdd5f1d88
-- title:
--   Lemma 5.3: active extensions with prescribed starting ranks, $E[N_k(A;G_a)\mid F_\theta,r(A)]\le(e/(a-\theta))^k$
-- statement:
--   Fix $0\le\theta<a$ and condition on $F_\theta$; let $A$ be a nonempty connected vertex set of $G_\theta$. Assign the ranks of all vertices of $A$ arbitrarily in $[a,\infty)$; outside $A$, the revealed ranks stay fixed and the unrevealed ranks are independent with distribution $\theta+\mathrm{Exp}(1)$. Let $N_k(A;G_a)$ be the number of $k$-sets $W\subseteq V(G)\setminus A$ attached to $A$ for which $A\cup W$ is active at time $a$. For each $k\ge0$,
--   $$
--   \mathbb E\big[N_k(A;G_a)\mid F_\theta,r(A)\big]\le\Big(\frac{e}{a-\theta}\Big)^k. \tag{22}
--   $$
--
--   This is the count behind the conditional bounds of Lemma 6.1. It holds on every finite simple graph.
--
--   **Formalization Note** The conditional expectation is the Lebesgue integral of $N_k$ under the explicit conditional law, stated together with the measurability of $N_k$.
--
--   Differences from the source:
--   - reading: conditioning on F_θ and r(A) (Lemma 5.3) → the measure `condLaw r₀ θ A rA` for every history r₀ at θ and every prescribed rA with values in [a, ∞) on A; reason: the explicit conditional law described in Lemma 5.3 and on p.18; holding for every history is the pointwise form of the conditional statement
--   - generalization: E[N_k(A; G_a) | F_θ, r(A)] ≤ (e/(a − θ))^k → measurability of N_k, and its lower Lebesgue integral ≤ (e/(a − θ))^k; reason: the added measurability clause is true and makes the lower integral the expectation; dropping it gives (22)
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Lemma 5.3, eq. (22), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Lemma 5.3 (Active extensions with prescribed starting ranks; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.20): fix `0 ≤ θ < a`,
condition on `F_θ`, and suppose that `A` is a non-empty connected vertex set of `G_θ`. Assign the
ranks of all vertices of `A` arbitrarily in `[a, ∞)`; outside `A`, the ranks revealed by `F_θ`
remain fixed, and the unrevealed ranks remain independent with distribution `θ + Exp(1)`. Then for
each `k ≥ 0`, `E[N_k(A; G_a) | F_θ, r(A)] ≤ (e/(a − θ))^k` (22).

**Formalization Note** The conditional law is `condLaw r₀ θ A rA`, and the statement holds for
every history `r₀` at time `θ` and every prescribed `rA`. `G_θ` is computed from the history.
The expectation is the lower Lebesgue integral of `N_k` plus a measurability clause. No degree
bound is assumed. -/
theorem lemma_5_3 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (k : ℕ) :
    Measurable (fun r : V → ℝ => Ncount G A k a r) ∧
    ∫⁻ r, (Ncount G A k a r : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤
      ENNReal.ofReal ((Real.exp 1 / (a - θ)) ^ k) := by sorry

end RGMISFast
