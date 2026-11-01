-- Prove2me | Theorems.Thm_ProcessingNetworks_DTMCFoster_lemma_C_25
-- name    : ProcessingNetworks.DTMCFoster.lemma_C_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:23.139825+00:00
-- url     : https://prove2.me/theorems/e42911d8-eb69-4209-a8c4-22ffc28c4d66
-- title:
--   Lemma C.25 — drift $PV\le V-f+b1_C$ bounds $\mathbb E_x\sum_{k<T_C}f(X_k)$ by $V(x)+b$
-- statement:
--   Let $X$ be a discrete-time Markov chain on a countable state space $\mathcal S$ with transition matrix $P$, write $PV(x)=\sum_{y}P_{xy}V(y)$, and for $C\subseteq\mathcal S$ let $T_C=\inf\{k\ge1:X_k\in C\}$ be the first passage time into $C$ ($T_C=\infty$ if $C$ is never entered). Suppose there are a constant $b>0$, a set $C\subseteq\mathcal S$ (not necessarily finite) and non-negative functions $V,f:\mathcal S\to\mathbb R_+$ such that
--   $$
--   PV(x)\le V(x)-f(x)+b\,1_C(x),\qquad x\in\mathcal S. \tag{C.21}
--   $$
--   Then
--   $$
--   \mathbb E_x\Big(\sum_{k=0}^{T_C-1}f(X_k)\Big)\le V(x)+b,\qquad x\in\mathcal S. \tag{C.22}
--   $$
--
--   With $f\equiv c>0$ this gives $c\,\mathbb E_x(T_C)\le V(x)+b$, the step from the drift condition to (C.17) in the standard Foster–Lyapunov criterion (Theorem C.26); applied to the chain sampled at the state-dependent times $n(x)$ it gives the state-dependent criterion (Theorem C.27).
--
--   **Formalization Note** As in Lemma C.24, the chain started at $x$ is a process on $(\Omega,\mathbb P)$ with the path law (C.3) and $X_0=x$ almost surely, and the expectation is the lower Lebesgue integral of a $[0,\infty]$-valued sum.
--
--   Differences from the source:
--   - encoding: E_x, the expectation for the DTMC started at x → a process X on a probability space (Ω, ℙ) with the path law (C.3) for P (IsJumpChain P X), ℙ{X₀ = x} = 1 and measurable events {X_k = s}; reason: this fixes the law of X to be ℙ_x; the X_k are random variables, as in §C.1
--   - encoding: non-negative functions 𝒮 → ℝ₊ and the constant b > 0 → functions S → ℝ≥0 and b : ℝ≥0 with 0 < b; reason: ℝ≥0 is ℝ₊; same instances
--   - encoding: PV(x) ≤ V(x) − f(x) + b1_C(x) (C.21), real inequality → Σ_y P(x, y) V(y) + f(x) ≤ V(x) + b·1_C(x) in [0, ∞]; reason: the book's right side is finite, so (C.21) forces PV(x) < ∞ and the two forms are equivalent
--   - encoding: T_C = inf{k ≥ 1 : X_k ∈ C} and E_x(Σ_{k=0}^{T_C−1} f(X_k)) → firstPassage X C ω ∈ ℕ∞ (∞ if C is never entered) and the lower Lebesgue integral of the [0, ∞]-valued sum over {k : k < T_C}; reason: the book's convention T_C = ∞ when C is not entered; nonnegative expectations may be infinite
--   - generalization: standing assumption of §C.8 (p.282) "Suppose that X is irreducible" → irreducibility is not assumed; reason: the proof of Lemma C.25 never uses irreducibility; on an irreducible chain the Lean statement is the book's
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability (pre-publication draft 2020-4-2, spnbook.org), Appendix C, §C.8, Lemma C.25 (C.21)–(C.22), p.283 (PDF p.299); T_C from (C.16), p.280 (PDF p.296)

import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_DTMCFoster_firstPassage

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory
open KellyStochasticNetworks.MaxWeight ProcessingNetworks.Stability

namespace ProcessingNetworks.DTMCFoster

/-- **Lemma C.25**, Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix C, §C.8, p.283, PDF p.299: "Suppose there exists a constant `b > 0`, a set
`C ⊂ 𝒮`, and two non-negative functions `V, f : 𝒮 → ℝ₊` such that
`PV(x) ≤ V(x) − f(x) + b 1_C(x)`, `x ∈ 𝒮` (C.21). Then
`E_x(Σ_{k=0}^{T_C−1} f(X_k)) ≤ V(x) + b`, `x ∈ 𝒮` (C.22)."

`T_C = inf{k ≥ 1 : X_k ∈ C}` is the first passage time (C.16), `∞` if `C` is never entered
(`firstPassage X C`). `C` is any subset of `𝒮` (finiteness is not assumed). `X` is a DTMC with
transition matrix `P` started at `x`: `IsJumpChain P X` (the path law (C.3)) and
`ℙ{X₀ = x} = 1`.

**Formalization Note** `PV(x) = Σ_y P(x, y) V(y)`; (C.21) is written additively in `[0, ∞]`,
`PV(x) + f(x) ≤ V(x) + b 1_C(x)`, which is the book's inequality (its right side is finite, so it
forces `PV(x) < ∞`). The expectation in (C.22) is the lower Lebesgue integral of the `[0, ∞]`-valued
sum over `{k : k < T_C}`. `b` is a positive element of `ℝ≥0`. Each `X_k` is a random variable: the
events `{X_k = s}` are measurable. -/
theorem lemma_C_25 {S Ω : Type*} [Countable S] [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (P : Chain S) (X : ℕ → Ω → S) (hX : IsJumpChain P X)
    (hXmeas : ∀ (k : ℕ) (s : S), MeasurableSet {ω | X k ω = s})
    (x : S) (hx0 : ℙ {ω | X 0 ω = x} = 1)
    (b : ℝ≥0) (hb : 0 < b) (C : Set S) (V f : S → ℝ≥0)
    (hdrift : ∀ y, (∑' z, P y z * (V z : ℝ≥0∞)) + f y ≤
      V y + C.indicator (fun _ => (b : ℝ≥0∞)) y) :
    ∫⁻ ω, ∑' k : ℕ,
        (if (k : ℕ∞) < firstPassage X C ω then (f (X k ω) : ℝ≥0∞) else 0) ≤
      (V x : ℝ≥0∞) + b := by sorry

end ProcessingNetworks.DTMCFoster
