-- Prove2me | Theorems.Thm_TabooRegen_btilde_dominating_bound
-- name    : TabooRegen.btilde_dominating_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:26.542+00:00
-- url     : https://prove2.me/theorems/8efaa8dc-db9a-4299-ae58-1d9dc976ed35
-- title:
--   Theorem 2, proof, p.287 — $|\tilde b_{B,\ell}(t)|\le h(0)e^{-\delta t}+h(\eta t/2)$ when $\lambda^{-1}\ell\le(1-\eta)t$
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense with $T(0)=0$ and satisfy A1–A4 and A7, with $h$ the dominating function of A4. For every $\eta\in(0,1)$ there is $\delta>0$ such that, uniformly in measurable $B$ and in $\ell\ge0$ and $t\ge0$ with $\lambda^{-1}\ell\le(1-\eta)t$,
--
--   $$
--   |\tilde b_{B,\ell}(t)|\le h(0)\,e^{-\delta t}+h\big(\tfrac{\eta t}{2}\big).
--   $$
--
--   This gives a bound on the kernels of (4.2) that decays as $t\to\infty$, uniformly in the window, as long as the window is not too wide.
--
--   Differences from the source:
--   - encoding: cycle moments $E[\cdot]$ in A1–A4, A7, $c_1$, $\lambda$ → written under $Q=P(\cdot\mid\Gamma\ge T(0))$; reason: with $T(0)=0$ this is $Q=P$
--   - encoding: complete separable metric space $S$ → Polish space with its Borel σ-algebra; reason: the same class of spaces
--   - encoding: $\tilde S=S\cup\{\Delta\}$ and $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → `S ⊕ Unit` with $\Delta$ = `Sum.inr ()` (isolated), the subtype of càdlàg paths with the trace of the cylinder σ-algebra; reason: for a separable metric $\tilde S$ the cylinder trace equals the Skorohod Borel σ-algebra (Ethier–Kurtz, Prop. 3.7.1)
--   - reading: $0=T(-1)\le T(0)<T(1)<\cdots$ (p.273) and $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → $T(n)\in[0,\infty]$ nondecreasing, strictly increasing while finite, $T(n)=\infty$ when $\Gamma<T(n)$, and $T(n)=\infty$ only then ($\Gamma<\infty$); reason: read literally the two requirements contradict each other once two consecutive times are infinite; this reading keeps both
--   - encoding: cycles $W_n$ defined from $X$ and the $T(n)$ → $W_n$ carried as data with its defining equation and measurability; reason: both follow from the càdlàg paths of $X$ and the measurability of the $T(n)$, so no instance changes
--   - encoding: Definition 2 as an identity of conditional laws given $T(0),\dots,T(n)$ on $\{\Gamma\ge T(n)\}$ → $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable $C$ (cycle sequences) and $H$ (values of $T(0..n)$); reason: this is the definition of that conditional law
--   - encoding: $\kappa_1,\kappa_2$ as suprema of real sets → suprema in `EReal`; reason: $\kappa_2=+\infty$ is a value, not the junk value of a real supremum
--   - reading: $\tilde b_{B,\ell}(t)=P(((W_{\ell+j+1}:|j|\le\ell),t-T(\ell))\in B,\ T(\ell)\le t<T(\ell+1),\ \Gamma>t)$ (p.286) → the same with the factor $e^{\alpha t}$; reason: the kernel convolved in (4.2) and bounded on p.287 ("$|\tilde b_{B,\ell}(t)|\le e^{\alpha t}P(\dots)$") carries this factor
--   - reading: $k(0)\exp(-\varepsilon\eta t/2+t\,o(\varepsilon^2))$ for $\varepsilon$ small, uniformly in $R$ → $h(0)e^{-\delta t}$ for some $\delta>0$, uniformly in $B$; reason: $R$ is a misprint for $B$ and $k$ is A4's $h$; choosing $\varepsilon$ small makes the exponent at most $-\delta t$
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 2, proof, p.287 (PDF p.17), "We conclude that uniformly in R and ℓ satisfying λ−1ℓ ⩽ (1 − η)t"

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **The dominating bound on `b̃`** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), Theorem 2, proof, p.287: "uniformly in `R` and
`ℓ` satisfying `λ⁻¹ℓ ⩽ (1 − η)t`, we have `|b̃B,ℓ(t)| ⩽ k(0) exp(−εηt/2 + to(ε²)) + k(ηt/2)`").
In the non-delayed case `T(0) = 0`, under the hypotheses of Theorem 2 with `h` the dominating
function of A4: for every `η ∈ (0, 1)` there is `δ > 0` such that for all measurable `B`,
`ℓ ∈ ℕ` and `t ⩾ 0` with `λ⁻¹ℓ ⩽ (1 − η)t`, `|b̃_{B,ℓ}(t)| ⩽ h(0) e^{−δt} + h(ηt/2)`.

**Formalization Note.** The printed `R` is `B`. The printed `exp(−εηt/2 + t o(ε²))` with `ε` small
is stated as `e^{−δt}` for some `δ > 0`. -/
theorem btilde_dominating_bound {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) {h : ℝ → ℝ} (h4 : M.A4With α h) (h7 : M.A7) :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ δ > 0, ∀ (ℓ : ℕ) (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)),
      MeasurableSet B → ∀ t : ℝ, 0 ≤ t → (M.lamInv α).toReal * ℓ ≤ (1 - η) * t →
        |M.btilde α ℓ B t| ≤ h 0 * Real.exp (-δ * t) + h (η * t / 2) := by sorry

end TabooRegen
