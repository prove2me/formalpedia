-- Prove2me | Theorems.Thm_TierneyMH_Peskun_theorem4_peskun_ordering
-- name    : TierneyMH.Peskun.theorem4_peskun_ordering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T12:52:29.814981+00:00
-- url     : https://prove2.me/theorems/f52bbcec-a35a-4135-9f5b-caf2bcbd222b
-- title:
--   Theorem 4 (Peskun's theorem on general state spaces): $P_1 \succeq P_2 \Rightarrow v(f,P_1) \le v(f,P_2)$
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space in which singletons are measurable, and let $\pi$ be a probability measure on $E$. Let $P_1$ and $P_2$ be Markov transition kernels on $E$ that are reversible with respect to $\pi$ (so $\pi$ is invariant for both), and let $f \in L^2_0(\pi) = \{g \in L^2(\pi) : \int g\, d\pi = 0\}$. For a transition kernel $H$ let
--
--   $$
--   v(f, H) \;=\; \lim_{n\to\infty} \frac{1}{n}\operatorname{Var}_H\Bigl(\sum_{i=1}^{n} f(X_i)\Bigr),
--   $$
--
--   where $X_0, X_1, \dots$ is a Markov chain with initial distribution $\pi$ and transition kernel $H$. If $P_1 \succeq P_2$, i.e. $P_1$ dominates $P_2$ off the diagonal, then both limits $v(f,P_1)$ and $v(f,P_2)$ exist in $[0,\infty]$ and
--
--   $$
--   v(f, P_1) \;\le\; v(f, P_2).
--   $$
--
--   This extends Peskun's (1973) finite-state theorem to general state spaces. The ergodic average of $f$ along a chain that moves off the diagonal more readily has asymptotic variance no larger than along the other chain. Combined with the maximality of the Metropolis–Hastings acceptance probability, this makes $\alpha_{MH}$ the optimal acceptance function in terms of asymptotic variance.
--
--   **Formalization Note** The asymptotic variance may be infinite, so variances are Mathlib's extended variances with values in $[0,\infty]$ and the division by $n$ is carried out in $[0,\infty]$. The existence of both limits, which the definition of $v$ presupposes and the paper's proof asserts ("the limit is guaranteed to exist, but it may be infinite", p. 6), is part of the conclusion. The path measure is the Ionescu–Tulcea trajectory measure of the chain started from $\pi$, and the sum runs over $X_1,\dots,X_n$, excluding $X_0$. Measurability of singletons is the paper's implicit assumption that $A\setminus\{x\}$ is an event, and $f$ is a measurable representative of its $L^2$ class.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 5, Theorem 4

import Mathlib
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Definitions.Def_TierneyMH_Peskun_chainMeasure

open TierneyMH.Shared

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace TierneyMH.Peskun

/-- **Theorem 4** (Tierney 1998, p. 5). Let `P₁ P₂` be reversible Markov kernels on `E` with
invariant distribution `π`, and let `f ∈ L²₀(π)`. For a kernel `H`, let
`v(f, H) = lim_{n→∞} (1/n) Var_H(∑_{i=1}^{n} f(X_i))`, where `X₀, X₁, …` is the Markov chain
with initial distribution `π` and kernel `H` (`chainMeasure π H`). If `P₁ ⪰ P₂`
(`OffDiagDominates π P₁ P₂`), then `v(f, P₁) ≤ v(f, P₂)`.

Both limits are asserted to exist in `[0, ∞]` (`ℝ≥0∞`-valued `evariance`, division in
`ℝ≥0∞`), which the definition of `v` presupposes and the proof asserts ("the limit is
guaranteed to exist, but it may be infinite", p. 6). `MeasurableSingletonClass E` is the
paper's implicit assumption that `A \ {x}` is an event. -/
theorem theorem4_peskun_ordering {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    (P₁ P₂ : Kernel E E) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (hrev₁ : Kernel.IsReversible P₁ π) (hrev₂ : Kernel.IsReversible P₂ π)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (hdom : OffDiagDominates π P₁ P₂) :
    ∃ v₁ v₂ : ℝ≥0∞,
      Tendsto (fun n : ℕ => evariance (pathSum f n) (chainMeasure π P₁) / n) atTop (𝓝 v₁) ∧
      Tendsto (fun n : ℕ => evariance (pathSum f n) (chainMeasure π P₂) / n) atTop (𝓝 v₂) ∧
      v₁ ≤ v₂ := by sorry

end TierneyMH.Peskun
