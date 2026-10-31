-- Prove2me | Theorems.Thm_SVFAppt_lemma_3_6
-- name    : SVFAppt.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:42.170305+00:00
-- url     : https://prove2.me/theorems/04766d63-e5db-4e26-92de-b9257237729e
-- title:
--   Lemma 3.6 — the maximum of a symmetric random walk is stochastically dominated by $|S_k|$
-- statement:
--   Let $Y_1,\dots,Y_k$ be independent integrable random variables on a probability space, each with a distribution symmetric about $0$ ($Y_i$ and $-Y_i$ have the same law). Let $S_j=Y_1+\cdots+Y_j$. Then:
--
--   1. $\max\{0,S_1,\dots,S_k\}$ is stochastically dominated by $|S_k|$:
--   $$P\big(\max\{0,S_1,\dots,S_k\}>a\big)\ \le\ P\big(|S_k|>a\big)\qquad\text{for every }a\in\mathbb R;$$
--   2. consequently
--   $$\mathbb E\max\{0,S_1,\dots,S_k\}\ \le\ \mathbb E|S_k|.$$
--
--   In the paper, under the symmetry Assumption 3.2 and the mean-based schedule, $W_{k+1}=\max\{0,S_1,\dots,S_k\}$ for the walk of the centred service times, so $\mathbb EW_{k+1}\le\mathbb E|X_{\tau(1)}+\cdots+X_{\tau(k)}|$; the proof of Theorem 3.4 applies the lemma to the symmetric steps $X_i-X_i'$.
--
--   **Formalization Note** Stochastic domination is the published usual stochastic order `UsualOrder` ($P(\cdot>a)$ for all real $a$).
--
--   Differences from the source:
--   - generalization: W_{k+1} of the model, steps X_τ(k), …, X_τ(1) with B_i symmetric about their means (Assumption 3.2) → any finite walk with independent integrable steps symmetric about 0; reason: the model's walk (eq_3_waiting_max, clause 2, with x = µ) and the walk of X_i − X′_i are instances
--   - reading: W_{k+1} is stochastically dominated by |S_k| → P(walk max > a) ⩽ P(|S_k| > a) for every real a; reason: the usual stochastic order; equivalent to the proof's P(· ⩾ a) form for a ⩾ 0 by right limits
--   - encoding: random variables (the model's B_i are independent with finite means) → each step a measurable, integrable function on a probability space; reason: Lean convention for a real random variable with a finite mean; every instance the paper uses (centred service times and their differences) satisfies it
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, Lemma 3.6, p. 16

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Definitions.Def_SVFAppt_walkMax

open MeasureTheory ProbabilityTheory

namespace SVFAppt

/-- **Lemma 3.6: the maximum of a symmetric walk is stochastically dominated by `|S_k|`.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, Lemma 3.6, p. 16: "Under the symmetry assumption, the
random variable Wk+1 is stochastically dominated by |Sk|, and thus
EWk+1 ⩽ E|Sk| = E|Xτ(1) + Xτ(2) + · · · + Xτ(k)|."

Let `Y 0, …, Y (k−1)` be independent integrable random variables on `(Ω, P)`, each with a
distribution symmetric about `0`, and `S = Y 0 + ⋯ + Y (k−1)`. Then
1. `max{0, S_1, …, S_k}` is smaller than `|S|` in the usual stochastic order:
   `P(max{0, S_1, …, S_k} > a) ⩽ P(|S| > a)` for every real `a`;
2. `E max{0, S_1, …, S_k} ⩽ E |S|`.

**Formalization Note** Stated for a general finite walk with symmetric independent steps (the
paper applies it to the centred service times under Assumption 3.2 and, in the proof of
Theorem 3.4, to the steps `X_i − X′_i`). Symmetry is equality of the laws of `Y i` and `−Y i`.
`UsualOrder` is the published usual stochastic order. -/
theorem lemma_3_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (Y : Fin k → Ω → ℝ) (hYm : ∀ i, Measurable (Y i)) (hYi : ∀ i, Integrable (Y i) P)
    (hind : iIndepFun Y P) (hsymm : ∀ i, P.map (Y i) = P.map (fun s => -Y i s)) :
    StochasticOrders.Usual.UsualOrder P P (fun s => walkMax (fun i => Y i s))
        (fun s => |∑ i, Y i s|) ∧
      ∫ s, walkMax (fun i => Y i s) ∂P ≤ ∫ s, |∑ i, Y i s| ∂P := by sorry

end SVFAppt
