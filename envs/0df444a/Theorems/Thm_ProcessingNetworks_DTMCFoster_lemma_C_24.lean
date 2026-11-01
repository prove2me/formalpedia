-- Prove2me | Theorems.Thm_ProcessingNetworks_DTMCFoster_lemma_C_24
-- name    : ProcessingNetworks.DTMCFoster.lemma_C_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:20.673698+00:00
-- url     : https://prove2.me/theorems/64bc28e9-65d8-4795-b47d-a2a8311d9303
-- title:
--   Lemma C.24 (Comparison theorem) — $\mathbb E_x\sum_{k<\tau}f(X_k)\le V(x)+\mathbb E_x\sum_{k<\tau}g(X_k)$
-- statement:
--   Let $X$ be a discrete-time Markov chain on a countable state space $\mathcal S$ with transition matrix $P$, and write $PV(x)=\sum_{y\in\mathcal S}P_{xy}V(y)$. Suppose that $V,f,g:\mathcal S\to\mathbb R_+$ are non-negative functions satisfying
--   $$
--   PV(x)\le V(x)-f(x)+g(x),\qquad x\in\mathcal S. \tag{C.18}
--   $$
--   Then for every stopping time $\tau$ with respect to $X$ (with values in $\mathbb Z_+\cup\{\infty\}$) and every state $x\in\mathcal S$,
--   $$
--   \mathbb E_x\Big(\sum_{k=0}^{\tau-1}f(X_k)\Big)\le V(x)+\mathbb E_x\Big(\sum_{k=0}^{\tau-1}g(X_k)\Big), \tag{C.19}
--   $$
--   where $\mathbb E_x$ is the expectation for the chain started at $x$ and both sides may be infinite.
--
--   The comparison theorem turns a one-step drift inequality into a bound on costs accumulated up to a random time; Lemma C.25 and the Foster–Lyapunov criteria are its consequences.
--
--   **Formalization Note** The chain started at $x$ is a process on a probability space $(\Omega,\mathbb P)$ whose finite-dimensional laws are those of (C.3) with transition matrix $P$ and with $X_0=x$ almost surely; expectations are lower Lebesgue integrals of $[0,\infty]$-valued sums.
--
--   Differences from the source:
--   - encoding: E_x, the expectation for the DTMC started at x → a process X on a probability space (Ω, ℙ) with the path law (C.3) for P (IsJumpChain P X), ℙ{X₀ = x} = 1 and measurable events {X_k = s}; reason: this fixes the law of X to be ℙ_x; the X_k are random variables, as in §C.1
--   - encoding: non-negative functions 𝒮 → ℝ₊ → functions S → ℝ≥0; reason: ℝ≥0 is ℝ₊; same instances
--   - encoding: PV(x) ≤ V(x) − f(x) + g(x) (C.18), real inequality → Σ_y P(x, y) V(y) + f(x) ≤ V(x) + g(x) in [0, ∞]; reason: the book's right side is finite, so (C.18) forces PV(x) < ∞ and the two forms are equivalent; the [0, ∞] form avoids Lean's value 0 for a divergent real series
--   - encoding: τ : Ω → ℤ₊ ∪ {∞} and E_x(Σ_{k=0}^{τ−1} ·) → τ : Ω → ℕ∞ and the lower Lebesgue integral of the [0, ∞]-valued sum over {k : k < τ}; reason: nonnegative series and expectations may be infinite, as the book's proof notes
--   - generalization: standing assumption of §C.8 (p.282) "Suppose that X is irreducible" → irreducibility is not assumed; reason: the proof of Lemma C.24 never uses irreducibility; on an irreducible chain the Lean statement is the book's
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability (pre-publication draft 2020-4-2, spnbook.org), Appendix C, §C.8, Lemma C.24 (C.18)–(C.19), p.282 (PDF p.298); stopping time, §C.2, p.276 (PDF p.292)

import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_DTMCFoster_IsStoppingTime

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory
open KellyStochasticNetworks.MaxWeight ProcessingNetworks.Stability

namespace ProcessingNetworks.DTMCFoster

/-- **Lemma C.24** (Comparison theorem), Dai & Harrison, *Processing Networks*, pre-publication
draft 2020-4-2, spnbook.org, Appendix C, §C.8, p.282, PDF p.298: "Suppose that
`V, f, g : 𝒮 → ℝ₊` are three non-negative functions satisfying
`PV(x) ≤ V(x) − f(x) + g(x)`, `x ∈ 𝒮` (C.18). Then for any stopping time `τ` and any state
`x ∈ 𝒮`, `E_x(Σ_{k=0}^{τ−1} f(X_k)) ≤ V(x) + E_x(Σ_{k=0}^{τ−1} g(X_k))` (C.19)."

Here `X` is a DTMC with transition matrix `P` started at `x`: on a probability space
`(Ω, ℙ)`, `X` satisfies the path law (C.3) with transition matrix `P` (`IsJumpChain P X`) and
`ℙ{X₀ = x} = 1`, so that `ℙ = ℙ_x` on events of `X`. The stopping time `τ` is that of §C.2, p.276
(`IsStoppingTime X τ`), with values in `ℤ₊ ∪ {∞}`.

**Formalization Note** `PV(x) = Σ_y P(x, y) V(y)`. All quantities are in `[0, ∞]`: (C.18) is
written additively, `PV(x) + f(x) ≤ V(x) + g(x)`, which is the book's inequality (its right side
`V(x) − f(x) + g(x)` is finite, so (C.18) forces `PV(x) < ∞`), and both expectations in (C.19) are
lower Lebesgue integrals of `[0, ∞]`-valued sums over `{k : k < τ}`, which may be infinite (the
proof notes that `E_x(Z_{τⁿ})` can be infinite). Each `X_k` is a random variable: the events
`{X_k = s}` are measurable. -/
theorem lemma_C_24 {S Ω : Type*} [Countable S] [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (P : Chain S) (X : ℕ → Ω → S) (hX : IsJumpChain P X)
    (hXmeas : ∀ (k : ℕ) (s : S), MeasurableSet {ω | X k ω = s})
    (x : S) (hx0 : ℙ {ω | X 0 ω = x} = 1)
    (V f g : S → ℝ≥0)
    (hdrift : ∀ y, (∑' z, P y z * (V z : ℝ≥0∞)) + f y ≤ V y + g y)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime X τ) :
    ∫⁻ ω, ∑' k : ℕ, (if (k : ℕ∞) < τ ω then (f (X k ω) : ℝ≥0∞) else 0) ≤
      (V x : ℝ≥0∞) + ∫⁻ ω, ∑' k : ℕ, (if (k : ℕ∞) < τ ω then (g (X k ω) : ℝ≥0∞) else 0) := by sorry

end ProcessingNetworks.DTMCFoster
