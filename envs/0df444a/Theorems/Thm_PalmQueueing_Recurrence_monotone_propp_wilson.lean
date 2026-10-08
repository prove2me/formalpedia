-- Prove2me | Theorems.Thm_PalmQueueing_Recurrence_monotone_propp_wilson
-- name    : PalmQueueing.Recurrence.monotone_propp_wilson
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T00:23:08.341264+00:00
-- url     : https://prove2.me/theorems/75292c1a-979e-48be-bece-1738ed39cc66
-- title:
--   Theorem 2.5.2 — the monotone Propp–Wilson algorithm
-- statement:
--   **Theorem 2.5.2.** The monotone backwards coalescence time $M$ is a.s. finite. Also, the
--   random variables $X^{-M}_0(1) = X^{-M}_0(r)$ have the distribution $\pi$.
--
--   Theorem 2.5.1 requires all $r$ chains to meet, which is prohibitively time-consuming when the
--   state space is large. If there is a partial order $\preceq$ on $E$ which the updating function
--   preserves,
--   $$ i \preceq j \;\Rightarrow\; h(i,\xi) \preceq h(j,\xi) \quad \forall \xi , \tag{2.5.11} $$
--   with $1 \preceq 2 \preceq \dots \preceq r$, and if a **single** updating sequence drives every
--   chain ($\xi_n(i) = \xi_n$ for all $n$ and $i$), then the two extremal chains funnel all the
--   others: for all $n \in \mathbb{Z}$, all $i \in E$,
--   $X^k_n(1) \preceq X^k_n(i) \preceq X^k_n(r)$ for all $k \ge n$. So the coalescence of **two**
--   chains suffices, and the resulting sample is still exactly $\pi$-distributed.
--
--   The finiteness of $M$ is immediate in this case: the forwards coupling time of the two chains
--   $\{X^0_n(1)\}$ and $\{X^0_n(r)\}$ is dominated by the first time $n \ge 0$ at which
--   $X^0_n(r) = 1$, which is finite by the recurrence assumption.
--
--   **Formalization Note.** The model is `CFTPMono`, in which one i.i.d. uniform sequence drives all
--   the chains. $\preceq$ is a partial order (reflexive, transitive, antisymmetric) with a least
--   element $1$ and a greatest element $r$, which is what $1 \preceq 2 \preceq \dots \preceq r$
--   supplies to the funnelling argument; it is preserved by the update (2.5.11); and the recurrence
--   assumption of the proof is the hypothesis that the chain started at time $0$ in state $r$ reaches
--   state $1$ in finite time a.s.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 113, Theorem 2.5.2

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_ExactSampling

/-!
# Theorem 2.5.2: the monotone Propp-Wilson algorithm (§2.5.3, p.113)
-/

namespace PalmQueueing.Recurrence

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.5.2** (p.113). The monotone backwards coalescence time `M` is a.s. finite. Also,
the random variables `X_0^{-M}(1) = X_0^{-M}(r)` have the distribution `π`.

Theorem 2.5.1 requires all `r` chains to meet, which is prohibitively slow when the state space is
large. If the state space carries a partial order `≼` that the updating function preserves,

`(2.5.11)  i ≼ j ⟹ h(i, ξ) ≼ h(j, ξ)  ∀ξ`,

with `1 ≼ 2 ≼ … ≼ r`, and if a **single** updating sequence drives every chain, then the two
extremal chains funnel all the others: `X^k_n(1) ≼ X^k_n(i) ≼ X^k_n(r)` for every `i` and every
`k ≥ n`. So the coalescence of two chains suffices, and the resulting sample is still **exactly**
`π`-distributed.

The hypotheses below are the book's. The model is `CFTPMono`, whose chains are all driven by
the single sequence `{ξ_n}`. `le` is the partial order `≼` (reflexive, transitive, antisymmetric),
and `bot` and `top` are its least and greatest elements, which is what the book's
`1 ≼ 2 ≼ … ≼ r` is used for in the funnelling argument; the update preserves `le` (2.5.11); and
`hrec` is the recurrence assumption the proof invokes: the chain started at the top state `r` at
time `0` reaches the bottom state `1` in finite time. -/
theorem monotone_propp_wilson {r : ℕ} (C : CFTPMono Ω r) (le : Fin r → Fin r → Prop)
    (hrefl : ∀ i, le i i) (htrans : ∀ i j k, le i j → le j k → le i k)
    (hantisymm : ∀ i j, le i j → le j i → i = j)
    (bot top : Fin r)
    (hbot : ∀ i, le bot i) (htop : ∀ i, le i top)
    (hpreserve : ∀ i j : Fin r, le i j → ∀ x : ℝ, le (C.h i x) (C.h j x))
    (hrec : ∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.X 0 n top ω = bot) :
    (∀ᵐ ω ∂C.P, ∃ n : ℕ, 1 ≤ n ∧ C.CoalescedExtremal bot top n ω) ∧
    ∀ Z : Ω → Fin r, Measurable Z →
      (∀ᵐ ω ∂C.P, ∀ n : ℕ, 1 ≤ n → C.CoalescedExtremal bot top n ω →
        Z ω = C.X (-(n : ℤ)) n bot ω) →
      ∀ j : Fin r, (C.P {ω | Z ω = j}).toReal = C.pi j := by sorry

end PalmQueueing.Recurrence
