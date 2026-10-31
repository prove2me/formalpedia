-- Prove2me | Theorems.Thm_TabooRegen_theorem_2
-- name    : TabooRegen.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:37.610189+00:00
-- url     : https://prove2.me/theorems/c42637f3-ed05-4411-bdfe-ec32fd861d14
-- title:
--   Theorem 2 — the window of cycles around $t$ and the age, given $\Gamma>t$, converge uniformly to the taboo limit $P^*$ (corrected: window centred on the straddling cycle $W_{N(t)+1}$)
-- statement:
--   Let $X$ be a process that is taboo-regenerative in the wide sense and satisfies A1–A7, and let $(k_t:t\ge0)$ be a deterministic non-negative nondecreasing integer-valued function with $\limsup_{t\to\infty}k_t/t<\lambda$. Then
--
--   $$
--   \sup_{B\in\mathcal D}\Big|P\Big(\big((W_{N(t)+1+j}:|j|\le k_t),\beta(t)\big)\in B,\ N(t)\ge k_t\ \Big|\ \Gamma>t\Big)-P^*\Big(\big((W_j:|j|\le k_t),\beta\big)\in B\Big)\Big|\longrightarrow0\qquad(t\to\infty).
--   $$
--
--   Here $N(t)=\max\{n:T(n)\le t\}$, $W_{N(t)+1}$ is the cycle straddling $t$, $\beta(t)=t-T(N(t))$ is its age, and $P^*$ is the two-sided taboo limit: fully tabooed, exponentially biased cycles before the origin, a specially biased straddling cycle with an exponentially distributed age, and ordinary cycles after it. The supremum runs over all measurable sets of windows and ages, the window may grow linearly in $t$ at any rate below $\lambda$, and the process may be delayed.
--
--   Conditioned on not having left $A$ by a large time $t$, the process near $t$, seen on the time scale of its regeneration cycles, therefore looks like a sample of $P^*$; this is the regenerative description of the quasi-stationary behaviour of $X$.
--
--   Differences from the source:
--   - correction: window $(W_{N(t)+j}:|j|\le k_t)$ → window $(W_{N(t)+1+j}:|j|\le k_t)$, centred on the cycle straddling $t$; reason: $W_{N(t)}$ is the last completed cycle, while $P^*$'s $W_0$ and the proof's (4.2) use the straddling cycle; counterexample to the printed index: $S=\{0,1\}$, $A=\{0\}$, $T(0)=0$, i.i.d. Exp(1) cycle lengths and fair coins, $X\equiv0$ on a cycle with heads and $X=0$ then $1$ on its two halves with tails ($\alpha=1/2$, $\lambda=1/2$, $\kappa_1=1/2<\kappa_2=1$, all of A1–A7 hold), $k_t\equiv0$, $B=\{$centre cycle visits $A^c\}$: the printed left side is $0$ for every $t$ while $P^*(B)=1/4$
--   - reading: cycle moments $E[\cdot]$ in A1–A4, A7, $c_1$, $\lambda$ and $P^*$ → under the cycle law $Q=P(\cdot\mid\Gamma\ge T(0))$; reason: in the delayed case the unconditioned law of $W_1$ also contains junk cycles after an exit during the delay; by Definition 2 ($n=0$) $Q$ is the law of the non-delayed version, and $Q=P$ when $T(0)=0$
--   - encoding: complete separable metric space $S$ → Polish space with its Borel σ-algebra; reason: the same class of spaces
--   - encoding: $\tilde S=S\cup\{\Delta\}$ and $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → `S ⊕ Unit` with $\Delta$ = `Sum.inr ()` (isolated), the subtype of càdlàg paths with the trace of the cylinder σ-algebra; reason: for a separable metric $\tilde S$ the cylinder trace equals the Skorohod Borel σ-algebra (Ethier–Kurtz, Prop. 3.7.1)
--   - reading: $0=T(-1)\le T(0)<T(1)<\cdots$ (p.273) and $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → $T(n)\in[0,\infty]$ nondecreasing, strictly increasing while finite, $T(n)=\infty$ when $\Gamma<T(n)$, and $T(n)=\infty$ only then ($\Gamma<\infty$); reason: read literally the two requirements contradict each other once two consecutive times are infinite; this reading keeps both
--   - encoding: cycles $W_n$ defined from $X$ and the $T(n)$ → $W_n$ carried as data with its defining equation and measurability; reason: both follow from the càdlàg paths of $X$ and the measurability of the $T(n)$, so no instance changes
--   - encoding: Definition 2 as an identity of conditional laws given $T(0),\dots,T(n)$ on $\{\Gamma\ge T(n)\}$ → $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable $C$ (cycle sequences) and $H$ (values of $T(0..n)$); reason: this is the definition of that conditional law
--   - encoding: $N(t)=\max\{n:T(n)\le t\}$ → `strad t` $=\min\{n\ge0:t<T(n)\}=N(t)+1$ (with $T(-1)=0$); $N(t)\ge k$ is `k < strad t`; reason: the same event; on the null explosion event the set is empty and the event is false
--   - encoding: $\kappa_1,\kappa_2$ as suprema of real sets → suprema in `EReal`; reason: $\kappa_2=+\infty$ is a value, not the junk value of a real supremum
--   - encoding: $(k_t:t\ge0)$ nondecreasing integer valued, $\overline{\lim}_{t\to\infty}k_t/t<\lambda$ → `k : ℝ → ℕ` monotone on $[0,\infty)$ with $\exists c<\lambda$, eventually $k_t\le ct$; reason: equivalent to the printed lim sup condition; values at $t<0$ play no role
--   - encoding: $\sup_{B\in\mathcal D}|\cdots|\to0$ → for every $\varepsilon>0$, eventually in $t$, $|\cdots|\le\varepsilon$ for every measurable $B$; reason: equivalent; avoids a supremum over a $t$-dependent type
--   - encoding: $P^*$, a probability on the bi-infinite $(W,\beta)$ defined by (4.1) and the change of measure of p.285 → its window laws `PstarWindow k`, the explicit formula obtained from (4.1) and p.285 with $n=k$; reason: the statement involves only finite windows
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 2, p.286 (PDF p.16)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **Theorem 2** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), p.286), with the window index corrected to the straddling cycle.
Let `X` be taboo-regenerative in the wide sense and satisfy A1–A7, and let `(k_t : t ⩾ 0)` be a
deterministic non-negative nondecreasing integer-valued function with `lim sup_{t→∞} k_t / t < λ`.
Then, as `t → ∞`,
`sup_{B ∈ 𝒟} |P(((W_{N(t)+1+j} : |j| ⩽ k_t), β(t)) ∈ B, N(t) ⩾ k_t | Γ > t)
  − P*(((W_j : |j| ⩽ k_t), β) ∈ B)| → 0`.

**Formalization Note.**
* Correction: the paper prints the window `W_{N(t)+j}`; the cycle straddling `t` is `W_{N(t)+1}`,
  which is the cycle `W₀` of `P*` and the one the proof's (4.2) uses. With the printed index the
  statement fails (two-state example, difference ⩾ 1/4); see the mission notes.
* The delay is allowed (`T(0)` random); A1–A4 and A7 are read under the cycle law
  `Q = P(· | Γ ⩾ T(0))`.
* `lim sup k_t / t < λ` is written `∃ c < λ, k_t ⩽ c t` eventually, which is equivalent.
* `sup_B |…| → 0` is written `∀ ε > 0`, eventually in `t`, `∀ B` measurable, `|…| ⩽ ε`; the window
  type depends on `t` through `k_t`.
* `P(· | Γ > t)` is `ProbabilityTheory.cond`; `P*` enters through its window law `PstarWindow`. -/
theorem theorem_2 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h2 : M.A2) (h3 : M.A3 α)
    (h4 : M.A4 α) (h5 : M.A5 α) (h6 : M.A6 α) (h7 : M.A7)
    (k : ℝ → ℕ) (hk : MonotoneOn k (Set.Ici 0))
    (hkg : ∃ c < M.rate α, ∀ᶠ t in atTop, (k t : ℝ) ≤ c * t) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ B : Set ((Fin (2 * k t + 1) → Path S) × ℝ), MeasurableSet B →
      |(ProbabilityTheory.cond M.P {ω | ENNReal.ofReal t < M.Γ ω}
          {ω | k t < M.strad t ω ∧ (M.win (k t) t ω, M.age t ω) ∈ B}).toReal -
        (M.PstarWindow α (k t) B).toReal| ≤ ε := by sorry

end TabooRegen
