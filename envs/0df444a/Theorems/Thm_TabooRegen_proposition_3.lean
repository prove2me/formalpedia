-- Prove2me | Theorems.Thm_TabooRegen_proposition_3
-- name    : TabooRegen.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:13.566353+00:00
-- url     : https://prove2.me/theorems/c17bde03-2a78-4733-b960-4b21d78c8ce6
-- title:
--   Proposition 3 — $P(\Gamma>t)\sim c_2e^{-\alpha t}$ with a delay (corrected: $c_2=E[e^{\alpha\tau_0};\Gamma\ge\tau_0]c_1$)
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense and satisfy A1–A6 (a delay $T(0)$ is allowed). Then
--
--   $$
--   P(\Gamma>t)\sim c_2e^{-\alpha t}\quad(t\to\infty),\qquad c_2=E\big[e^{\alpha\tau_0};\ \Gamma\ge\tau_0\big]\,c_1\in(0,\infty),
--   $$
--
--   where $c_1$ is the constant of Proposition 2, computed under the cycle law $Q=P(\cdot\mid\Gamma\ge T(0))$.
--
--   It extends Proposition 2 to delayed processes; in the main theorem it supplies the denominator $P(\Gamma>t)$ when $T(0)$ is random.
--
--   Differences from the source:
--   - correction: $c_2=E[\exp(\alpha\tau_0);\ \Gamma>\tau_0]\,c_1$ → $c_2=E[\exp(\alpha\tau_0);\ \Gamma\ge\tau_0]\,c_1$; reason: the regeneration at $T(0)$ factors over $\{\Gamma\ge T(0)\}$; counterexample to the printed constant: $T(0)=1$, $X=0\in A$ on $[0,1)$, then i.i.d. Exp(1) cycles on which $X\equiv0$ or $X\equiv1\in A^c$ with probability $1/2$ each (A1–A6 hold with $\alpha=1/2$, $c_1=1/2$): $e^{\alpha t}P(\Gamma>t)\to e^{1/2}/2$, the printed $c_2$ is $e^{1/2}/4$
--   - reading: cycle moments $E[\cdot]$ in A1–A4, A7, $c_1$, $\lambda$ and $P^*$ → under the cycle law $Q=P(\cdot\mid\Gamma\ge T(0))$; reason: in the delayed case the unconditioned law of $W_1$ also contains junk cycles after an exit during the delay; by Definition 2 ($n=0$) $Q$ is the law of the non-delayed version, and $Q=P$ when $T(0)=0$
--   - encoding: complete separable metric space $S$ → Polish space with its Borel σ-algebra; reason: the same class of spaces
--   - encoding: $\tilde S=S\cup\{\Delta\}$ and $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → `S ⊕ Unit` with $\Delta$ = `Sum.inr ()` (isolated), the subtype of càdlàg paths with the trace of the cylinder σ-algebra; reason: for a separable metric $\tilde S$ the cylinder trace equals the Skorohod Borel σ-algebra (Ethier–Kurtz, Prop. 3.7.1)
--   - reading: $0=T(-1)\le T(0)<T(1)<\cdots$ (p.273) and $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → $T(n)\in[0,\infty]$ nondecreasing, strictly increasing while finite, $T(n)=\infty$ when $\Gamma<T(n)$, and $T(n)=\infty$ only then ($\Gamma<\infty$); reason: read literally the two requirements contradict each other once two consecutive times are infinite; this reading keeps both
--   - encoding: cycles $W_n$ defined from $X$ and the $T(n)$ → $W_n$ carried as data with its defining equation and measurability; reason: both follow from the càdlàg paths of $X$ and the measurability of the $T(n)$, so no instance changes
--   - encoding: Definition 2 as an identity of conditional laws given $T(0),\dots,T(n)$ on $\{\Gamma\ge T(n)\}$ → $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable $C$ (cycle sequences) and $H$ (values of $T(0..n)$); reason: this is the definition of that conditional law
--   - encoding: $P(\Gamma>t)\sim c\,e^{-\alpha t}$ → $c>0$ and $e^{\alpha t}P(\Gamma>t)\to c$; reason: equivalent for a positive constant, and positivity is what makes $\sim$ meaningful
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Proposition 3, p.278 (PDF p.8)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **Proposition 3** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), p.278), with the constant corrected. Under A1–A6,
`P(Γ > t) ∼ c₂ exp(−αt)` as `t → ∞`, where `c₂ = E[exp(ατ₀); Γ ⩾ τ₀] c₁`.

**Formalization Note.**
* Correction: the paper prints `c₂ = E[exp(ατ₀); Γ > τ₀] c₁`. When a cycle can start in `Aᶜ`
  (`Q(γ₁ = 0) > 0`) this is off by the factor `Q(γ₁ > 0)`: with `T(0) = 1`, `X = 0 ∈ A` on `[0, 1)`
  and i.i.d. `Exp(1)` cycles that stay in `A` or sit in `Aᶜ` with probability `1/2` each, `α = 1/2`,
  `c₁ = 1/2` and `e^{αt} P(Γ > t) → e^{1/2}/2`, while the printed `c₂` is `e^{1/2}/4`.
* `c₁` is computed under the cycle law `Q = P(· | Γ ⩾ T(0))`, as are A1–A4.
* `∼` is written `c₂ > 0` and `e^{αt} P(Γ > t) → c₂`. -/
theorem proposition_3 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) {α : ℝ} (h1 : M.A1 α) (h2 : M.A2) (h3 : M.A3 α)
    (h4 : M.A4 α) (h5 : M.A5 α) (h6 : M.A6 α) :
    0 < M.c2 α ∧
      Tendsto (fun t : ℝ => Real.exp (α * t) * (M.P {ω | ENNReal.ofReal t < M.Γ ω}).toReal)
        atTop (𝓝 (M.c2 α)) := by sorry

end TabooRegen
