-- Prove2me | Theorems.Thm_SVFAppt_convex_le_sub_indep
-- name    : SVFAppt.convex_le_sub_indep
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:07.374135+00:00
-- url     : https://prove2.me/theorems/4c82c241-1d10-43ce-889c-c190706c8282
-- title:
--   Proof of Theorem 3.4, p. 17 — $X\le_{\mathrm{cx}}X-X'$ for an independent mean-zero $X'$
-- statement:
--   Let $X$ and $X'$ be independent integrable random variables on a probability space with $\mathbb EX'=0$. Then
--
--   $$X\ \le_{\mathrm{cx}}\ X-X'.$$
--
--   In the paper $X_i=B_i-\mu_i$ and $X_i'$ is an independent copy of $X_i$; since $\mathbb E[X_i-X_i'\mid X_i]=X_i$, Strassen's theorem (Lemma 2.5) gives $X_i\le_{\mathrm{cx}}X_i-X_i'$. This symmetrization step lets the proof of Theorem 3.4 replace arbitrary centred steps by symmetric ones, to which Lemma 3.6 applies.
--
--   **Formalization Note** The convex order is the published `ConvexOrder` (integrable test functions).
--
--   Differences from the source:
--   - generalization: X′_i an independent copy of the centred X_i = B_i − µ_i → any integrable X and any independent integrable X′ with E X′ = 0; reason: an independent copy of a mean-zero variable is such an X′
--   - encoding: A ⩽cx B: Eφ(A) ⩽ Eφ(B) for all convex φ for which the expectations exist → published ConvexOrder: ∫φ(A) ⩽ ∫φ(B) for every convex φ with φ∘A, φ∘B integrable; reason: for integrable A, B the two are equivalent (monotone approximation of φ by Lipschitz convex functions)
--   - encoding: random variables (the model's B_i are independent with finite means) → each step a measurable, integrable function on a probability space; reason: Lean convention for a real random variable with a finite mean; every instance the paper uses (centred service times and their differences) satisfies it
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, proof of Theorem 3.4, p. 17

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

open MeasureTheory ProbabilityTheory

namespace SVFAppt

/-- **Adding an independent mean-zero noise increases the convex order: `X ⩽cx X − X′`.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, proof of Theorem 3.4, p. 17: "Let X′1, X′2, . . . , X′n
have the same distributions as respectively X1, X2, . . . , Xn such that all these random variables
are independent. […] As E[Xi − X′i|Xi] = Xi, we see using Lemma 2.5 that Xi ⩽cx Xi − X′i."

Let `X`, `X′` be independent integrable random variables on a probability space `(Ω, P)` with
`E X′ = 0`. Then `X ⩽cx X − X′`.

**Formalization Note** Stated for any independent mean-zero `X′`; the paper's `X′_i` (an
independent copy of the centred `X_i`) is a special case. `ConvexOrder` is the published
integrable-`φ` convex order. -/
theorem convex_le_sub_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X X' : Ω → ℝ) (hXm : Measurable X) (hX'm : Measurable X')
    (hXi : Integrable X P) (hX'i : Integrable X' P)
    (hind : IndepFun X X' P) (hmean : ∫ s, X' s ∂P = 0) :
    StochasticOrders.Convex.ConvexOrder P P X (fun s => X s - X' s) := by sorry

end SVFAppt
