-- Prove2me | Theorems.Thm_TabooRegen_renewal_decomposition_4_2
-- name    : TabooRegen.renewal_decomposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:17.771149+00:00
-- url     : https://prove2.me/theorems/1c9caa1b-fb5e-4a68-be95-e7981b58c430
-- title:
--   Display (4.2) — the renewal decomposition of the tabooed window probability (corrected: straddling window, $\Gamma\ge u$)
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense with $T(0)=0$ and satisfy A1–A4 and A7. For every $k\ge0$, $t\ge0$ and measurable $B$,
--
--   $$
--   e^{\alpha t}P\Big(\big((W_{N(t)+1+j}:|j|\le k),\beta(t)\big)\in B,\ N(t)\ge k,\ \Gamma>t\Big)=\sum_{j=0}^{\infty}\int_{[0,t]}\tilde G^{(j)}(du)\,\tilde b_{B,k}(t-u),
--   $$
--
--   where $\tilde G^{(j)}$ is the $j$-fold convolution of $\tilde G$ and $\tilde b_{B,k}(s)=e^{\alpha s}P(((W_{k+j+1}:|j|\le k),s-T(k))\in B,\ T(k)\le s<T(k+1),\ \Gamma>s)$. Moreover, for every $j\ge0$,
--
--   $$
--   \tilde G^{(j)}(du)=e^{\alpha u}P\big(T(j)\in du,\ \Gamma\ge T(j)\big).
--   $$
--
--   This turns the tabooed window probability into a renewal convolution with the proper renewal measure $\sum_j\tilde G^{(j)}$, to which the key renewal theorem applies.
--
--   Differences from the source:
--   - correction: window $(W_{N(t)+j}:|j|\le k_t)$ → window $(W_{N(t)+1+j}:|j|\le k_t)$, centred on the cycle straddling $t$; reason: $W_{N(t)}$ is the last completed cycle, while $P^*$'s $W_0$ and the proof's (4.2) use the straddling cycle; counterexample to the printed index: $S=\{0,1\}$, $A=\{0\}$, $T(0)=0$, i.i.d. Exp(1) cycle lengths and fair coins, $X\equiv0$ on a cycle with heads and $X=0$ then $1$ on its two halves with tails ($\alpha=1/2$, $\lambda=1/2$, $\kappa_1=1/2<\kappa_2=1$, all of A1–A7 hold), $k_t\equiv0$, $B=\{$centre cycle visits $A^c\}$: the printed left side is $0$ for every $t$ while $P^*(B)=1/4$
--   - correction: middle expression of (4.2) with $P(T(j)\in du,\ \Gamma>u)$ → $e^{\alpha u}P(T(j)\in du,\ \Gamma\ge T(j))=\tilde G^{(j)}(du)$; reason: the regeneration at $T(j)$ factors over $\{\Gamma\ge T(j)\}$; with $\Gamma>u$ the middle expression loses the factor $P(\gamma_1>0)$, e.g. for i.i.d. cycles that start in $A^c$ with probability $1/2$, $j=0$, $u=0$: $P(T(0)\in\{0\},\Gamma>0)=1/2$ while $\tilde G^{(0)}\{0\}=1$
--   - encoding: cycle moments $E[\cdot]$ in A1–A4, A7, $c_1$, $\lambda$ → written under $Q=P(\cdot\mid\Gamma\ge T(0))$; reason: with $T(0)=0$ this is $Q=P$
--   - encoding: complete separable metric space $S$ → Polish space with its Borel σ-algebra; reason: the same class of spaces
--   - encoding: $\tilde S=S\cup\{\Delta\}$ and $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → `S ⊕ Unit` with $\Delta$ = `Sum.inr ()` (isolated), the subtype of càdlàg paths with the trace of the cylinder σ-algebra; reason: for a separable metric $\tilde S$ the cylinder trace equals the Skorohod Borel σ-algebra (Ethier–Kurtz, Prop. 3.7.1)
--   - reading: $0=T(-1)\le T(0)<T(1)<\cdots$ (p.273) and $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → $T(n)\in[0,\infty]$ nondecreasing, strictly increasing while finite, $T(n)=\infty$ when $\Gamma<T(n)$, and $T(n)=\infty$ only then ($\Gamma<\infty$); reason: read literally the two requirements contradict each other once two consecutive times are infinite; this reading keeps both
--   - encoding: cycles $W_n$ defined from $X$ and the $T(n)$ → $W_n$ carried as data with its defining equation and measurability; reason: both follow from the càdlàg paths of $X$ and the measurability of the $T(n)$, so no instance changes
--   - encoding: Definition 2 as an identity of conditional laws given $T(0),\dots,T(n)$ on $\{\Gamma\ge T(n)\}$ → $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable $C$ (cycle sequences) and $H$ (values of $T(0..n)$); reason: this is the definition of that conditional law
--   - encoding: $N(t)=\max\{n:T(n)\le t\}$ → `strad t` $=\min\{n\ge0:t<T(n)\}=N(t)+1$ (with $T(-1)=0$); $N(t)\ge k$ is `k < strad t`; reason: the same event; on the null explosion event the set is empty and the event is false
--   - encoding: $\kappa_1,\kappa_2$ as suprema of real sets → suprema in `EReal`; reason: $\kappa_2=+\infty$ is a value, not the junk value of a real supremum
--   - encoding: $\sum_{j\ge0}\int_{[0,t]}\tilde G^{(j)}(du)\cdots$ → integral over $[0,t]$ against `renewalMeasure δ₀ G̃` $=\sum_j\delta_0*\tilde G^{*j}$; reason: the same measure
--   - reading: $\tilde b_{B,\ell}(t)=P(((W_{\ell+j+1}:|j|\le\ell),t-T(\ell))\in B,\ T(\ell)\le t<T(\ell+1),\ \Gamma>t)$ (p.286) → the same with the factor $e^{\alpha t}$; reason: the kernel convolved in (4.2) and bounded on p.287 ("$|\tilde b_{B,\ell}(t)|\le e^{\alpha t}P(\dots)$") carries this factor
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 2, proof, display (4.2), p.286 (PDF p.16)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **Display (4.2)** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), Theorem 2, proof, display (4.2), p.286). In the non-delayed
case `T(0) = 0`, under the hypotheses of Theorem 2, for every `k`, `t ⩾ 0` and measurable `B`,
`e^{αt} P(((W_{N(t)+1+j} : |j| ⩽ k), β(t)) ∈ B, N(t) ⩾ k, Γ > t)
  = Σ_{j ⩾ 0} ∫_{[0,t]} G̃^{(j)}(du) b̃_{B,k}(t − u)`,
where `b̃_{B,k}(s) = e^{αs} P(((W_{k+j+1} : |j| ⩽ k), s − T(k)) ∈ B, T(k) ⩽ s < T(k+1), Γ > s)`.

The second equality of (4.2) rests on the identity
`G̃^{(j)}(du) = e^{αu} P(T(j) ∈ du, Γ ⩾ T(j))`, which is stated as the second clause.

**Formalization Note.** Corrections: the left side uses the window centred on the straddling cycle
`W_{N(t)+1}`, which is what the right side computes (the paper's left side prints `W_{N(t)+j}`);
and the middle expression of (4.2) prints `P(T(j) ∈ du, Γ > u)`, which must read `Γ ⩾ u`
(it loses the factor `P(γ₁ > 0)` when a cycle can start in `Aᶜ`).
`Σ_j G̃^{(j)}` is the renewal measure `renewalMeasure δ₀ G̃` of the referenced
`SmithRegenerative.Equilibrium`. The factor `e^{αs}` is part of `b̃` (`btilde`). -/
theorem renewal_decomposition_4_2 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) (h4 : M.A4 α) (h7 : M.A7) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (B : Set ((Fin (2 * k + 1) → Path S) × ℝ)) (hB : MeasurableSet B) :
    Real.exp (α * t) *
        (M.P {ω | k < M.strad t ω ∧ (M.win k t ω, M.age t ω) ∈ B ∧
          ENNReal.ofReal t < M.Γ ω}).toReal =
      ∫ u in Set.Icc 0 t, M.btilde α k B (t - u)
        ∂(SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) (M.Gtilde α)) ∧
    ∀ j : ℕ, ((M.P.restrict {ω | M.T j ω ≤ M.Γ ω}).map fun ω => (M.T j ω).toReal).withDensity
        (fun u => ENNReal.ofReal (Real.exp (α * u))) =
      QueueingFundamentals.MG1.convPow (M.Gtilde α) j := by sorry

end TabooRegen
