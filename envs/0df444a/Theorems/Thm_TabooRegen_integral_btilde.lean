-- Prove2me | Theorems.Thm_TabooRegen_integral_btilde
-- name    : TabooRegen.integral_btilde
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:26.522403+00:00
-- url     : https://prove2.me/theorems/62d4cca6-dec7-4373-92a4-4cbe04dd1777
-- title:
--   Theorem 2, proof, p.288 — $\int_0^\infty\tilde b_{B,\ell}$ is the unnormalized $P^*$ window mass
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense with $T(0)=0$ and satisfy A1–A4 and A7. For every $\ell\ge0$ and measurable $B$,
--
--   $$
--   \int_0^\infty\tilde b_{B,\ell}(u)\,du=E\Big[e^{\alpha(\tau_1+\cdots+\tau_\ell)}\mathbf 1\{\Gamma\ge T(\ell)\}\int_0^{\tau_{\ell+1}\wedge\gamma_{\ell+1}}e^{\alpha x}\,\mathbf 1\{((W_1,\dots,W_{2\ell+1}),x)\in B\}\,dx\Big],
--   $$
--
--   the numerator of the window law $P^*(((W_j:|j|\le\ell),\beta)\in B)$, whose denominator $E\int_0^{\tau_1\wedge\gamma_1}e^{\alpha u}du$ is the numerator of $c_1$. With the previous milestone and Proposition 2 this identifies the limit: $\lambda\int_0^\infty\tilde b_{B,k_t}/c_1=P^*(((W_j:|j|\le k_t),\beta)\in B)$, which is the step the paper summarizes as "Utilizing proposition 2 then yields the desired result."
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
--   - encoding: the identification of the limit with $P^*$ (not displayed in the paper) → the identity of $\int_0^\infty\tilde b_{B,\ell}$ with the unnormalized window mass `PstarNum`, in $[0,\infty]$; reason: this is the Fubini step behind "Utilizing proposition 2 then yields the desired result"; stated without division so no integrability condition enters
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 2, proof, p.288 (PDF p.18), last sentence, with the change of measure of p.285

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **Identification of the limit** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), Theorem 2, proof, p.288, "Utilizing proposition 2
then yields the desired result", with the change of measure of p.285). In the non-delayed case
`T(0) = 0`, under the hypotheses of Theorem 2, for every `ℓ` and measurable `B`,
`∫₀^∞ b̃_{B,ℓ}(u) du = E[e^{α(τ₁+⋯+τ_ℓ)} 1{Γ ⩾ T(ℓ)} ∫₀^{τ_{ℓ+1}∧γ_{ℓ+1}} e^{αx}
  1{((W₁, …, W_{2ℓ+1}), x) ∈ B} dx]`,
the numerator of `P*_ℓ(B)`; the denominator `E ∫₀^{τ₁∧γ₁} e^{αu} du` is the numerator of `c₁`.

**Formalization Note.** Stated as an identity of extended non-negative reals (`PstarNum`), so no
integrability side condition enters. With Proposition 2 and the previous milestone it gives
`λ ∫₀^∞ b̃_{B,ℓ} / c₁ = P*_ℓ(B)`. -/
theorem integral_btilde {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) (h4 : M.A4 α) (h7 : M.A7) (ℓ : ℕ)
    (B : Set ((Fin (2 * ℓ + 1) → Path S) × ℝ)) (hB : MeasurableSet B) :
    ∫⁻ u in Set.Ioi 0, ENNReal.ofReal (M.btilde α ℓ B u) = M.PstarNum α ℓ B := by sorry

end TabooRegen
