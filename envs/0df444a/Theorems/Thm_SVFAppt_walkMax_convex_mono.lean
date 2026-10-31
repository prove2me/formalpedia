-- Prove2me | Theorems.Thm_SVFAppt_walkMax_convex_mono
-- name    : SVFAppt.walkMax_convex_mono
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:38.527588+00:00
-- url     : https://prove2.me/theorems/e08cb710-df1d-41c8-ba8e-b1800e178eed
-- title:
--   Proof of Theorem 3.4, p. 17 — the expected walk maximum is monotone in the convex order of independent steps
-- statement:
--   Let $Y_1,\dots,Y_k$ be independent integrable random variables on a probability space $(\Omega,P)$ and $Z_1,\dots,Z_k$ independent integrable random variables on a probability space $(\Omega',P')$, with
--
--   $$Y_i\le_{\mathrm{cx}}Z_i\qquad\text{for every }i.$$
--
--   Write $S_j(Y)=Y_1+\cdots+Y_j$ and likewise for $Z$. Then
--
--   $$\mathbb E\max\{0,S_1(Y),\dots,S_k(Y)\}\ \le\ \mathbb E\max\{0,S_1(Z),\dots,S_k(Z)\}.$$
--
--   The paper uses this twice: the walk maximum $W_{k+1}=\max\{0,S_1,\dots,S_k\}$ is convex in each step, so replacing a step $X_i$ by a step larger in the convex order (by $X_i-X_i'$ in the proof of Theorem 3.4; by $X_i$ in place of $X_j$, $j<i$, in the proof of Lemma 3.5) increases the expected waiting time.
--
--   **Formalization Note** The convex order is the published `ConvexOrder` (integrable test functions).
--
--   Differences from the source:
--   - generalization: the steps X_i of the model's walk replaced by X_i − X′_i (resp. X_i by X_j), on one probability space → any two independent integrable families Y, Z with Y_i ⩽cx Z_i, on possibly different probability spaces; reason: both uses in the paper are instances of this statement
--   - encoding: A ⩽cx B: Eφ(A) ⩽ Eφ(B) for all convex φ for which the expectations exist → published ConvexOrder: ∫φ(A) ⩽ ∫φ(B) for every convex φ with φ∘A, φ∘B integrable; reason: for integrable A, B the two are equivalent (monotone approximation of φ by Lipschitz convex functions)
--   - encoding: random variables (the model's B_i are independent with finite means) → each step a measurable, integrable function on a probability space; reason: Lean convention for a real random variable with a finite mean; every instance the paper uses (centred service times and their differences) satisfies it
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, proof of Theorem 3.4, p. 17 (also proof of Lemma 3.5, p. 15)

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder
import Definitions.Def_SVFAppt_walkMax

open MeasureTheory ProbabilityTheory

namespace SVFAppt

/-- **The expected walk maximum is monotone in the convex order of independent steps.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, proof of Theorem 3.4, p. 17: "Note that
Wk+1 = max{0, S1, . . . , Sk} is a convex function in Xi, as it is the maximum of functions linear
in Xi. Therefore, each time we replace a step Xi with a step Xi − X′i the expected maximum of the
random walk will increase"; the same claim is used in the proof of Lemma 3.5, p. 15.

Let `Y 0, …, Y (k−1)` be independent integrable random variables on `(Ω, P)` and
`Z 0, …, Z (k−1)` independent integrable random variables on `(Ω', P')` with `Y i ⩽cx Z i` for
every `i`. Then `E max{0, S_1(Y), …, S_k(Y)} ⩽ E max{0, S_1(Z), …, S_k(Z)}`.

**Formalization Note** Stated for a general finite walk (the paper applies it to the steps
`X_i` vs `X_i − X′_i`, and to `X_j` vs `X_i`); the steps may live on different probability
spaces. `ConvexOrder` is the published integrable-`φ` convex order. -/
theorem walkMax_convex_mono {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {k : ℕ} (Y : Fin k → Ω → ℝ) (Z : Fin k → Ω' → ℝ)
    (hYm : ∀ i, Measurable (Y i)) (hZm : ∀ i, Measurable (Z i))
    (hYi : ∀ i, Integrable (Y i) P) (hZi : ∀ i, Integrable (Z i) P')
    (hYind : iIndepFun Y P) (hZind : iIndepFun Z P')
    (hcx : ∀ i, StochasticOrders.Convex.ConvexOrder P P' (Y i) (Z i)) :
    ∫ s, walkMax (fun i => Y i s) ∂P ≤ ∫ s, walkMax (fun i => Z i s) ∂P' := by sorry

end SVFAppt
