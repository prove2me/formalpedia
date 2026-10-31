-- Prove2me | Theorems.Thm_TabooRegen_proposition_2
-- name    : TabooRegen.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:13.555298+00:00
-- url     : https://prove2.me/theorems/7668c84b-db55-4430-94d6-a083e92d3341
-- title:
--   Proposition 2 — $P(\Gamma>t)\sim c_1e^{-\alpha t}$ for a non-delayed taboo-regenerative process
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense and satisfy A1–A4, with $T(0)=0$. Then
--
--   $$
--   P(\Gamma>t)\sim c_1e^{-\alpha t}\quad(t\to\infty),\qquad c_1=\frac{E\int_0^{\gamma_1\wedge\tau_1}e^{\alpha s}\,ds}{E[\tau_1e^{\alpha\tau_1}I_1]}\in(0,\infty).
--   $$
--
--   For $\alpha>0$ the constant equals the printed $c_1=E[\exp(\alpha(\gamma_1\wedge\tau_1))-1]/(\alpha E[\tau_1\exp(\alpha\tau_1)I_1])$.
--
--   This exponential tail of the exit time is what makes conditioning on $\{\Gamma>t\}$ tractable: it identifies the normalization of the taboo limit and is used in the last step of the proof of Theorem 2.
--
--   Differences from the source:
--   - encoding: complete separable metric space $S$ → Polish space with its Borel σ-algebra; reason: the same class of spaces
--   - encoding: $\tilde S=S\cup\{\Delta\}$ and $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → `S ⊕ Unit` with $\Delta$ = `Sum.inr ()` (isolated), the subtype of càdlàg paths with the trace of the cylinder σ-algebra; reason: for a separable metric $\tilde S$ the cylinder trace equals the Skorohod Borel σ-algebra (Ethier–Kurtz, Prop. 3.7.1)
--   - reading: $0=T(-1)\le T(0)<T(1)<\cdots$ (p.273) and $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → $T(n)\in[0,\infty]$ nondecreasing, strictly increasing while finite, $T(n)=\infty$ when $\Gamma<T(n)$, and $T(n)=\infty$ only then ($\Gamma<\infty$); reason: read literally the two requirements contradict each other once two consecutive times are infinite; this reading keeps both
--   - encoding: cycles $W_n$ defined from $X$ and the $T(n)$ → $W_n$ carried as data with its defining equation and measurability; reason: both follow from the càdlàg paths of $X$ and the measurability of the $T(n)$, so no instance changes
--   - encoding: Definition 2 as an identity of conditional laws given $T(0),\dots,T(n)$ on $\{\Gamma\ge T(n)\}$ → $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable $C$ (cycle sequences) and $H$ (values of $T(0..n)$); reason: this is the definition of that conditional law
--   - encoding: cycle moments $E[\cdot]$ in A1–A4, A7, $c_1$, $\lambda$ → written under $Q=P(\cdot\mid\Gamma\ge T(0))$; reason: with $T(0)=0$ this is $Q=P$
--   - reading: $c_1=E[\exp(\alpha(\gamma_1\wedge\tau_1))-1]/(\alpha E[\tau_1\exp(\alpha\tau_1)I_1])$ → $c_1=E\int_0^{\gamma_1\wedge\tau_1}e^{\alpha s}ds/E[\tau_1e^{\alpha\tau_1}I_1]$, the form computed in the proof; reason: equal for $\alpha>0$; at $\alpha=0$, which A1 allows, the printed form is $0/0$
--   - encoding: $P(\Gamma>t)\sim c\,e^{-\alpha t}$ → $c>0$ and $e^{\alpha t}P(\Gamma>t)\to c$; reason: equivalent for a positive constant, and positivity is what makes $\sim$ meaningful
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Proposition 2, p.277 (PDF p.7)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **Proposition 2** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), p.277). Suppose that `X` is taboo-regenerative in the wide
sense and satisfies A1–A4. Then, if `T(0) = 0`, `P(Γ > t) ∼ c₁ exp(−αt)` as `t → ∞`, where
`c₁ = E ∫₀^{γ₁∧τ₁} e^{αs} ds / E[τ₁ exp(ατ₁) I₁]`.

**Formalization Note.** `c₁` is the form computed in the proof (p.277); it equals the printed
`E[exp(α(γ₁ ∧ τ₁)) − 1] / (α E[τ₁ exp(ατ₁) I₁])` for `α > 0` and is defined at `α = 0`, where the
printed form is `0/0`. `P(Γ > t) ∼ c₁ e^{−αt}` is written `c₁ > 0` and `e^{αt} P(Γ > t) → c₁`. -/
theorem proposition_2 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α) (h2 : M.A2)
    (h3 : M.A3 α) (h4 : M.A4 α) :
    0 < M.c1 α ∧
      Tendsto (fun t : ℝ => Real.exp (α * t) * (M.P {ω | ENNReal.ofReal t < M.Γ ω}).toReal)
        atTop (𝓝 (M.c1 α)) := by sorry

end TabooRegen
