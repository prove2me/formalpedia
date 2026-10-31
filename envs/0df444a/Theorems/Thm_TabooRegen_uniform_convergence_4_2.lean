-- Prove2me | Theorems.Thm_TabooRegen_uniform_convergence_4_2
-- name    : TabooRegen.uniform_convergence_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:38.790849+00:00
-- url     : https://prove2.me/theorems/ad51b63d-693e-4524-a2d5-85fd1e43b7e8
-- title:
--   Theorem 2, proof, p.288 — (4.2) is uniformly close to $\lambda\int_0^\infty\tilde b_{B,k_t}$ (corrected: window centred on the straddling cycle $W_{N(t)+1}$)
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense with $T(0)=0$ and satisfy A1–A4 and A7, and let $(k_t)$ be nondecreasing, integer valued, with $\limsup_{t\to\infty}k_t/t<\lambda$. Then, uniformly in measurable $B$,
--
--   $$
--   \Big|e^{\alpha t}P\Big(\big((W_{N(t)+1+j}:|j|\le k_t),\beta(t)\big)\in B,\ N(t)\ge k_t,\ \Gamma>t\Big)-\frac{\int_0^\infty\tilde b_{B,k_t}(u)\,du}{\int_{[0,\infty)}u\,\tilde G(du)}\Big|\longrightarrow0\qquad(t\to\infty).
--   $$
--
--   This is the uniform renewal limit of (4.2); dividing by $e^{\alpha t}P(\Gamma>t)\to c_1$ and identifying the limit gives Theorem 2.
--
--   Differences from the source:
--   - correction: the window of (4.2) as printed, $(W_{N(t)+j}:|j|\le k_t)$ → $(W_{N(t)+1+j}:|j|\le k_t)$; reason: the right side of (4.2) computes the window centred on the straddling cycle; see the correction of Theorem 2
--   - encoding: cycle moments $E[\cdot]$ in A1–A4, A7, $c_1$, $\lambda$ → written under $Q=P(\cdot\mid\Gamma\ge T(0))$; reason: with $T(0)=0$ this is $Q=P$
--   - encoding: complete separable metric space $S$ → Polish space with its Borel σ-algebra; reason: the same class of spaces
--   - encoding: $\tilde S=S\cup\{\Delta\}$ and $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → `S ⊕ Unit` with $\Delta$ = `Sum.inr ()` (isolated), the subtype of càdlàg paths with the trace of the cylinder σ-algebra; reason: for a separable metric $\tilde S$ the cylinder trace equals the Skorohod Borel σ-algebra (Ethier–Kurtz, Prop. 3.7.1)
--   - reading: $0=T(-1)\le T(0)<T(1)<\cdots$ (p.273) and $T(n)=\infty$ on $\{\Gamma<T(n)\}$ (p.275) → $T(n)\in[0,\infty]$ nondecreasing, strictly increasing while finite, $T(n)=\infty$ when $\Gamma<T(n)$, and $T(n)=\infty$ only then ($\Gamma<\infty$); reason: read literally the two requirements contradict each other once two consecutive times are infinite; this reading keeps both
--   - encoding: cycles $W_n$ defined from $X$ and the $T(n)$ → $W_n$ carried as data with its defining equation and measurability; reason: both follow from the càdlàg paths of $X$ and the measurability of the $T(n)$, so no instance changes
--   - encoding: Definition 2 as an identity of conditional laws given $T(0),\dots,T(n)$ on $\{\Gamma\ge T(n)\}$ → $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable $C$ (cycle sequences) and $H$ (values of $T(0..n)$); reason: this is the definition of that conditional law
--   - encoding: $N(t)=\max\{n:T(n)\le t\}$ → `strad t` $=\min\{n\ge0:t<T(n)\}=N(t)+1$ (with $T(-1)=0$); $N(t)\ge k$ is `k < strad t`; reason: the same event; on the null explosion event the set is empty and the event is false
--   - encoding: $\kappa_1,\kappa_2$ as suprema of real sets → suprema in `EReal`; reason: $\kappa_2=+\infty$ is a value, not the junk value of a real supremum
--   - reading: $\tilde b_{B,\ell}(t)=P(((W_{\ell+j+1}:|j|\le\ell),t-T(\ell))\in B,\ T(\ell)\le t<T(\ell+1),\ \Gamma>t)$ (p.286) → the same with the factor $e^{\alpha t}$; reason: the kernel convolved in (4.2) and bounded on p.287 ("$|\tilde b_{B,\ell}(t)|\le e^{\alpha t}P(\dots)$") carries this factor
--   - encoding: $(k_t:t\ge0)$ nondecreasing integer valued, $\overline{\lim}_{t\to\infty}k_t/t<\lambda$ → `k : ℝ → ℕ` monotone on $[0,\infty)$ with $\exists c<\lambda$, eventually $k_t\le ct$; reason: equivalent to the printed lim sup condition; values at $t<0$ play no role
--   - encoding: $\sup_{B\in\mathcal D}|\cdots|\to0$ → for every $\varepsilon>0$, eventually in $t$, $|\cdots|\le\varepsilon$ for every measurable $B$; reason: equivalent; avoids a supremum over a $t$-dependent type
--   - encoding: $1/\int_{[0,\infty)}u\,\tilde G(du)$ → $\lambda$ (`rate`) $=1/E[\tau_1e^{\alpha\tau_1}I_1]$; reason: the same number
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 2, proof, p.288 (PDF p.18)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **Uniform convergence of (4.2)** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), Theorem 2, proof, p.288: "the difference
between (4.2) and `∫0^∞ b̃B,kt(u) du / ∫[0,∞) u G̃(du)` goes to zero uniformly in `B`"). In the
non-delayed case `T(0) = 0`, under the hypotheses of Theorem 2,
`sup_B |e^{αt} P(((W_{N(t)+1+j} : |j| ⩽ k_t), β(t)) ∈ B, N(t) ⩾ k_t, Γ > t) − λ ∫₀^∞ b̃_{B,k_t}(u) du| → 0`.

**Formalization Note.** `1 / ∫ u G̃(du) = λ` (`rate`). The window is centred on the straddling
cycle, as in (4.2). `sup … → 0` is written `∀ ε > 0`, eventually in `t`, `∀ B` measurable. -/
theorem uniform_convergence_4_2 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S]
    {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) (h4 : M.A4 α) (h7 : M.A7)
    (k : ℝ → ℕ) (hk : MonotoneOn k (Set.Ici 0))
    (hkg : ∃ c < M.rate α, ∀ᶠ t in atTop, (k t : ℝ) ≤ c * t) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ B : Set ((Fin (2 * k t + 1) → Path S) × ℝ), MeasurableSet B →
      |Real.exp (α * t) *
          (M.P {ω | k t < M.strad t ω ∧ (M.win (k t) t ω, M.age t ω) ∈ B ∧
            ENNReal.ofReal t < M.Γ ω}).toReal -
        M.rate α * ∫ u in Set.Ioi 0, M.btilde α (k t) B u| ≤ ε := by sorry

end TabooRegen
