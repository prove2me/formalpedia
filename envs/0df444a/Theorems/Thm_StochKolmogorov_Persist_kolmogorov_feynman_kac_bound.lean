-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_kolmogorov_feynman_kac_bound
-- name    : StochKolmogorov.Persist.kolmogorov_feynman_kac_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-01T00:47:47.660697+00:00
-- url     : https://prove2.me/theorems/c4470bd1-aa1d-4802-9e1e-4994138354be
-- title:
--   Feynman-Kac supermartingale bound for the Lyapunov function of a stochastic Kolmogorov system with a killing clock
-- statement:
--   Let $Y$ solve the stochastic Kolmogorov system $dY_i=Y_if_i(Y)\,dt+Y_ig_i(Y)\,dE_i$ from $x\in\mathbb R^{n,\circ}_+$ under Assumption 1.1 (with $c,\gamma_b$), let $\delta_0$ satisfy (3.2), $H$ be the constant of (3.5), $p\in\mathbb R^{n,\circ}_+$ with $\|p\|_1\le\delta_0$, $V(x)=(1+c^\top x)/\prod_i x_i^{p_i}$ and $0<\theta\le\delta_0$, $0\le\lambda\le1$. Let $\kappa\ge0$ be a bounded continuous killing rate with $\theta(H+\gamma_b)\le(1-\lambda)\kappa(z)$ wherever $R(z):=c\text{-bracket}(z)+\gamma_b\big(1+\sum_i(|f_i(z)|+g_i^2(z))\big)>0$, and put $A_t=\int_0^t\kappa(Y_v)\,dv$. Then for every $t\ge0$
--
--   $$\mathbb E\Big[e^{\gamma_b\theta t-A_t}V^\theta(Y_t)+\lambda\int_0^t\kappa(Y_u)\,e^{\gamma_b\theta u-A_u}V^\theta(Y_u)\,du\Big]\le V^\theta(x).$$
--
--   Role: the Feynman-Kac (killed generator) estimate in the proof of (4.18) of Theorem 4.1: on $\{R\le0\}$ the bound $\mathcal L V^\theta\le-\gamma_b\theta V^\theta$ of (3.3) holds, and on $\{R>0\}$ (a compact set) the killing rate absorbs the growth $\theta H V^\theta$.
--
--   **Formalization Note**: the expectation is a lower Lebesgue integral of `ENNReal.ofReal`; time integrals are interval integrals over $[0,t]$ with the path read at `toNNReal`.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Theorem 4.1, derivation of (4.18), p. 18, using (3.3) and (3.5) of Lemma 3.1 (p. 8); B. Oksendal, Stochastic Differential Equations, 6th ed., Springer 2003, https://doi.org/10.1007/978-3-642-14394-6, Theorem 8.2.1 (Feynman-Kac formula)

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Persist

open EthierKurtz

theorem kolmogorov_feynman_kac_bound {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B) {c p : SDEState n} {γb δ₀ θ lam : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (hθ : 0 < θ) (hθδ : θ ≤ δ₀) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ 1) {κ : SDEState n → ℝ} (hκc : Continuous κ) (hκ0 : ∀ z, 0 ≤ κ z) {N : ℝ}
    (hκN : ∀ z, κ z ≤ N)
    (hκR : ∀ z ∈ openOrthant n, 0 < cBracket C c z + γb * (1 + ∑ i, (|C.f i z| + C.g i z ^ 2)) →
      θ * (Hconst C c γb δ₀ + γb) ≤ (1 - lam) * κ z)
    {x : SDEState n} (hx : x ∈ openOrthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) :
    ∫⁻ ω, (ENNReal.ofReal (Real.exp (γb * θ * t - ∫ v in (0 : ℝ)..(t : ℝ), κ (Y v.toNNReal ω)) *
        Vfun c p (Y t ω) ^ θ) +
      ENNReal.ofReal (∫ u in (0 : ℝ)..(t : ℝ), lam * (κ (Y u.toNNReal ω) *
        (Real.exp (γb * θ * (u.toNNReal : ℝ) - ∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ),
          κ (Y v.toNNReal ω)) * Vfun c p (Y u.toNNReal ω) ^ θ)))) ∂P ≤
      ENNReal.ofReal (Vfun c p x ^ θ) := by sorry

end StochKolmogorov.Persist
