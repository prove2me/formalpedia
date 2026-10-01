-- Prove2me | Theorems.Thm_TierneyMH_Peskun_lemma3_positive_operator
-- name    : TierneyMH.Peskun.lemma3_positive_operator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T12:28:07.418576+00:00
-- url     : https://prove2.me/theorems/f2298aac-f1a9-41e5-9157-f68cff81097a
-- title:
--   Lemma 3: off-diagonal domination makes $P_2 - P_1$ a positive operator on $L^2(\pi)$
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space in which singletons are measurable, let $\pi$ be a probability measure on $E$, and let $P_1, P_2$ be Markov transition kernels on $E$ which both have $\pi$ as an invariant distribution. Suppose $P_1 \succeq P_2$, i.e. $P_1$ dominates $P_2$ off the diagonal. Then $P_2 - P_1$ is a positive operator on $L^2(\pi)$: for every $f \in L^2(\pi)$,
--
--   $$
--   \langle (P_2 - P_1) f, f\rangle \;=\; \iint f(x) f(y)\,\bigl(P_2(x, dy) - P_1(x, dy)\bigr)\,\pi(dx) \;\ge\; 0 .
--   $$
--
--   Equivalently, the lag-one autocovariances satisfy $\mathbb E_{P_1}[f(X_0)f(X_1)] \le \mathbb E_{P_2}[f(X_0)f(X_1)]$ for stationary chains started from $\pi$. This is the only place where off-diagonal domination enters the proof of Theorem 4. Only invariance, not reversibility, is assumed.
--
--   **Formalization Note** The double integral is written as $\int f(x)f(y)\,(\pi\otimes P_2)(dx,dy) - \int f(x)f(y)\,(\pi\otimes P_1)(dx,dy)$ with the joint laws $\pi \otimes P_i$. Both have both marginals equal to $\pi$ by invariance, so $f(x)f(y)$ is integrable against each and the Bochner integrals are genuine. Measurability of singletons is the paper's implicit assumption that $A\setminus\{x\}$ is an event, and $f$ is taken to be a measurable representative of its $L^2$ class.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 5, Lemma 3

import Mathlib
import Definitions.Def_TierneyMH_Shared_OffDiagDominates

open TierneyMH.Shared

open MeasureTheory ProbabilityTheory

namespace TierneyMH.Peskun

/-- **Lemma 3** (Tierney 1998, p. 5). Let `P₁ P₂` be Markov kernels on `E` with invariant
distribution `π` (invariance only, not reversibility, as printed), and suppose `P₁ ⪰ P₂`
(`OffDiagDominates π P₁ P₂`). Then `P₂ − P₁` is a positive operator on `L²(π)`: for every
`f ∈ L²(π)`,
`⟨(P₂ − P₁) f, f⟩ = ∬ f(x) f(y) (P₂(x, dy) − P₁(x, dy)) π(dx) ≥ 0`.
The double integral against `P₂(x, dy) − P₁(x, dy)` is written as the difference of the
integrals of `f(x) f(y)` against the joint laws `π ⊗ₘ P₂` and `π ⊗ₘ P₁`; both have marginals
`π` by invariance, so `f(x) f(y)` is integrable against each and neither integral is Lean's
junk value `0`. `MeasurableSingletonClass E` is the paper's implicit assumption that
`A \ {x}` is an event; `Measurable f` picks a measurable version of the `L²` class. -/
theorem lemma3_positive_operator {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    (P₁ P₂ : Kernel E E) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (hinv₁ : Kernel.Invariant P₁ π) (hinv₂ : Kernel.Invariant P₂ π)
    (hdom : OffDiagDominates π P₁ P₂)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) :
    0 ≤ (∫ p, f p.1 * f p.2 ∂(π ⊗ₘ P₂)) - ∫ p, f p.1 * f p.2 ∂(π ⊗ₘ P₁) := by sorry

end TierneyMH.Peskun
