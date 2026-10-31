-- Prove2me | Theorems.Thm_TabooRegen_btilde_le_conv
-- name    : TabooRegen.btilde_le_conv
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:18.922505+00:00
-- url     : https://prove2.me/theorems/a36b6f92-cdf2-41e9-8be1-7bc71fbc45e0
-- title:
--   Theorem 2, proof, p.287 — $|\tilde b_{B,\ell}(t)|\le\int_{[0,t]}\tilde G^{(\ell)}(du)\,h(t-u)$
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense with $T(0)=0$ and satisfy A1–A4 and A7, with $h$ the dominating function of A4. Uniformly in measurable $B$ and in $\ell\ge0$, for $t\ge0$,
--
--   $$
--   |\tilde b_{B,\ell}(t)|\le e^{\alpha t}P\big(T(\ell)\le t<T(\ell+1),\ \Gamma>t\big)=\int_{[0,t]}\tilde G^{(\ell)}(du)\,e^{\alpha(t-u)}P\big(\Gamma^\circ\wedge\tau_1>t-u\big)\le\int_{[0,t]}\tilde G^{(\ell)}(du)\,h(t-u).
--   $$
--
--   Here $\Gamma^\circ=\Gamma$ because $T(0)=0$. The last integral is $E^*[h(t-T(\ell));\ T(\ell)\le t]$, since under the taboo limit the sum of $\ell$ fully tabooed cycle lengths has law $\tilde G^{(\ell)}$. This is the first step towards a uniform dominating function for the kernels of (4.2).
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
--   - encoding: $E^*[k(t-T(\ell));\ T(\ell)\le t]$ and the dominating function $k(\cdot)$ → $\int_{[0,t]}h(t-u)\,\tilde G^{(\ell)}(du)$ with $h$ the function of A4; reason: under $P^*$, $T(\ell)$ has law $\tilde G^{(\ell)}$; the paper writes $k$ for the function it calls $h$ in A4
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 2, proof, first display of p.287 (PDF p.17)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **The first bound on `b̃`** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), Theorem 2, proof, first display of p.287). In the
non-delayed case `T(0) = 0`, under the hypotheses of Theorem 2 with `h` the dominating function of
A4, uniformly in `B` and `ℓ`, for `t ⩾ 0`,
`|b̃_{B,ℓ}(t)| ⩽ e^{αt} P(T(ℓ) ⩽ t < T(ℓ + 1), Γ > t)
  = ∫_{[0,t]} G̃^{(ℓ)}(du) e^{α(t−u)} P(Γ° ∧ τ₁ > t − u) ⩽ ∫_{[0,t]} G̃^{(ℓ)}(du) h(t − u)`.

**Formalization Note.** `G̃^{(ℓ)}` is `convPow G̃ ℓ`. The paper writes `k(·)` for the dominating
function and adds the equivalent form `E*[k(t − T(ℓ)); T(ℓ) ⩽ t]` (under `P*` the sum `T(ℓ)` of
`ℓ` fully tabooed cycle lengths has law `G̃^{(ℓ)}`); the integral form is stated. With `T(0) = 0`,
`Γ° = Γ`. -/
theorem btilde_le_conv {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) {h : ℝ → ℝ} (h4 : M.A4With α h) (h7 : M.A7) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B) (t : ℝ) (ht : 0 ≤ t) :
    |M.btilde α ℓ B t| ≤ Real.exp (α * t) * (M.P {ω | M.T ℓ ω ≤ ENNReal.ofReal t ∧
        ENNReal.ofReal t < M.T (ℓ + 1) ω ∧ ENNReal.ofReal t < M.Γ ω}).toReal ∧
    Real.exp (α * t) * (M.P {ω | M.T ℓ ω ≤ ENNReal.ofReal t ∧
        ENNReal.ofReal t < M.T (ℓ + 1) ω ∧ ENNReal.ofReal t < M.Γ ω}).toReal =
      ∫ u in Set.Icc 0 t, Real.exp (α * (t - u)) *
          (M.P {ω | ENNReal.ofReal (t - u) < min (M.Γ ω) (M.τ 1 ω)}).toReal
        ∂(QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ) ∧
    ∫ u in Set.Icc 0 t, Real.exp (α * (t - u)) *
          (M.P {ω | ENNReal.ofReal (t - u) < min (M.Γ ω) (M.τ 1 ω)}).toReal
        ∂(QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ) ≤
      ∫ u in Set.Icc 0 t, h (t - u) ∂(QueueingFundamentals.MG1.convPow (M.Gtilde α) ℓ) := by sorry

end TabooRegen
