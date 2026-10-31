-- Prove2me | Theorems.Thm_TabooRegen_exp_moment_of_A7
-- name    : TabooRegen.exp_moment_of_A7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:30.918594+00:00
-- url     : https://prove2.me/theorems/84cfbad5-faec-4907-a2e4-5d7b03afa86f
-- title:
--   Theorem 2, proof, p.287 — A7 gives $\tilde G$ an exponential moment
-- statement:
--   Let A1 and A7 hold. Then there is $\varepsilon_0>0$ with
--
--   $$
--   \int e^{\varepsilon_0x}\,\tilde G(dx)<\infty .
--   $$
--
--   Under the taboo limit the fully tabooed cycle lengths have law $\tilde G$, so this is the paper's "$E^*\exp(\varepsilon\tau_1)<\infty$ for $\varepsilon$ in a neighborhood of the origin" (finiteness at $\varepsilon_0$ gives it on $(-\infty,\varepsilon_0]$ since $\tilde G$ lives on $[0,\infty)$). It feeds the Chernoff bound on the number of tabooed cycles before $t$.
--
--   Differences from the source:
--   - reading: cycle moments $E[\cdot]$ in A1–A4, A7, $c_1$, $\lambda$ and $P^*$ → under the cycle law $Q=P(\cdot\mid\Gamma\ge T(0))$; reason: in the delayed case the unconditioned law of $W_1$ also contains junk cycles after an exit during the delay; by Definition 2 ($n=0$) $Q$ is the law of the non-delayed version, and $Q=P$ when $T(0)=0$
--   - encoding: complete separable metric space $S$ → Polish space with its Borel σ-algebra; reason: the same class of spaces
--   - encoding: $\tilde S=S\cup\{\Delta\}$ and $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → `S ⊕ Unit` with $\Delta$ = `Sum.inr ()` (isolated), the subtype of càdlàg paths with the trace of the cylinder σ-algebra; reason: for a separable metric $\tilde S$ the cylinder trace equals the Skorohod Borel σ-algebra (Ethier–Kurtz, Prop. 3.7.1)
--   - reading: $0=T(-1)\le T(0)<T(1)<\cdots$ (p.273) and $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → $T(n)\in[0,\infty]$ nondecreasing, strictly increasing while finite, $T(n)=\infty$ when $\Gamma<T(n)$, and $T(n)=\infty$ only then ($\Gamma<\infty$); reason: read literally the two requirements contradict each other once two consecutive times are infinite; this reading keeps both
--   - encoding: cycles $W_n$ defined from $X$ and the $T(n)$ → $W_n$ carried as data with its defining equation and measurability; reason: both follow from the càdlàg paths of $X$ and the measurability of the $T(n)$, so no instance changes
--   - encoding: Definition 2 as an identity of conditional laws given $T(0),\dots,T(n)$ on $\{\Gamma\ge T(n)\}$ → $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable $C$ (cycle sequences) and $H$ (values of $T(0..n)$); reason: this is the definition of that conditional law
--   - encoding: $\kappa_1,\kappa_2$ as suprema of real sets → suprema in `EReal`; reason: $\kappa_2=+\infty$ is a value, not the junk value of a real supremum
--   - encoding: $E^*\exp(\varepsilon\tau_{-1})<\infty$ for $\varepsilon$ near $0$ → $\exists\varepsilon_0>0$, $\int e^{\varepsilon_0x}\tilde G(dx)<\infty$; reason: $\tau_{-1}$ has law $\tilde G$ under $P^*$, and $\tilde G$ lives on $[0,\infty)$
--   - generalization: under the hypotheses of Theorem 2 (Definition 2, A1–A7) → under A1 and A7 only; reason: the sentence names A7 and $\alpha$ comes from A1; the statement specializes to the paper's setting
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 2, proof, p.287 (PDF p.17), "Recall that A7 ensures that E∗ exp(ετ1) < ∞ for ε in a neighborhood of the origin"

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **A7 gives an exponential moment of `G̃`** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), Theorem 2, proof, p.287: "Recall that
A7 ensures that `E∗exp(ετ1) < ∞` for `ε` in a neighborhood of the origin"). Under A1 and A7 there
is `ε₀ > 0` with `∫ e^{ε₀ x} G̃(dx) < ∞`.

**Formalization Note.** Under `P*` the fully tabooed cycle lengths have law `G̃`, so
`E* exp(ετ₋₁) = ∫ e^{εx} G̃(dx)`. Since `G̃` lives on `[0, ∞)`, finiteness at `ε₀` gives it on all
of `(−∞, ε₀]`, i.e. on a neighbourhood of the origin. -/
theorem exp_moment_of_A7 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    {α : ℝ} (h1 : M.A1 α) (h7 : M.A7) :
    ∃ ε₀ > 0, ∫⁻ x, ENNReal.ofReal (Real.exp (ε₀ * x)) ∂(M.Gtilde α) < ⊤ := by sorry

end TabooRegen
