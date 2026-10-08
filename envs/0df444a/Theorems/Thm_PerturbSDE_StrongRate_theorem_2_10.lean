-- Prove2me | Theorems.Thm_PerturbSDE_StrongRate_theorem_2_10
-- name    : PerturbSDE.StrongRate.theorem_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:14.158003+00:00
-- url     : https://prove2.me/theorems/46eaf932-9977-4aeb-b71c-68e94bbcd3df
-- title:
--   Theorem 2.10, p. 13 — perturbation estimate (43) (finite-dimensional case H = ℝ^d, U = ℝ^m)
-- statement:
--   Let $T\in(0,\infty)$, a stochastic basis with normal filtration, a standard $m$-dimensional $(\mathcal F_t)$-Brownian motion $W$, a Borel set $\mathcal O\subseteq\mathbb R^d$, measurable $\mu:\mathbb R^d\to\mathbb R^d$, $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$, $\varepsilon\in[0,\infty]$, $p\in[2,\infty)$ and a stopping time $\tau:\Omega\to[0,T]$ be given. Let $X,Y:[0,T]\times\Omega\to\mathcal O$ be adapted with continuous sample paths, and $a,b,\chi$ predictable ($\mathbb R^d$-, $\mathbb R^{d\times m}$- and $\mathbb R$-valued), with
--   $$\int_0^T\|a_s\|+\|b_s\|^2_{HS}+\|\mu(X_s)\|+\|\sigma(X_s)\|^2_{HS}+\|\mu(Y_s)\|+\|\sigma(Y_s)\|^2_{HS}\,ds<\infty\quad\mathbb P\text{-a.s.},$$
--   $X_t=X_0+\int_0^t\mu(X_s)ds+\int_0^t\sigma(X_s)dW_s$, $Y_t=Y_0+\int_0^ta_sds+\int_0^tb_sdW_s$, and, with $R_{p,\varepsilon}$ the monotonicity ratio,
--   $$\int_0^\tau\big[R_{p,\varepsilon}(X_s,Y_s)+\chi_s\big]^+ds<\infty\quad\mathbb P\text{-a.s.}\tag{42}$$
--   Then for all $r,q\in(0,\infty]$ with $\frac1p+\frac1q=\frac1r$,
--   $$\|X_\tau-Y_\tau\|_{L^r(\Omega)}\le\Big\|\exp\Big(\int_0^\tau\big[R_{p,\varepsilon}(X_s,Y_s)+\chi_s\big]^+ds\Big)\Big\|_{L^q(\Omega)}\Big[\Big\|p\|X-Y\|^{p-2}\big[\langle X-Y,\mu(Y)-a\rangle+\tfrac{(p-1)(1+1/\varepsilon)}{2}\|b-\sigma(Y)\|^2_{HS}-\chi\|X-Y\|^2\big]^+\Big\|^{1/p}_{L^1([\![0,\tau]\!])}+\|X_0-Y_0\|_{L^p(\Omega)}\Big].$$
--
--   The estimate controls the distance between an exact solution $X$ and an arbitrary Itô process $Y$ (for instance a numerical approximation) by an exponential moment of the one-sided monotonicity ratio times the local errors $a-\mu(Y)$, $b-\sigma(Y)$; no global monotonicity of $\mu,\sigma$ is assumed.
--
--   **Formalization Note** Finite-dimensional case $H=\mathbb R^d$, $U=\mathbb R^m$ of the paper's Hilbert-space statement, with the Hilbert–Schmidt norm on $\sigma$. All norms, moments and the right-hand side are in $[0,\infty]$, with $0\cdot\infty=0$, $0/0=0$, $1/0=\infty$ and $\exp(\infty)=\infty$; the ratio is computed in `EReal`. $X$ and $Y$ are the published `IsSolution` / `IsItoProcess` (continuous on $[0,T]$, adapted to the $\mathbb P$-completed filtration; the normal filtration is right-continuity plus completion; $W$ is a Brownian motion on $[0,\infty)$); the paper's integrability hypothesis is also stated explicitly. $a,b,\chi$ are predictable with respect to $(\mathcal F_t)$. The $L^1([\![0,\tau]\!])$ norm is the integral against $\lambda\otimes\mathbb P$ restricted to $\{(t,\omega):0\le t\le\tau(\omega)\}$.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, p. 13, Theorem 2.10, (42), (43)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_PerturbSDE_StrongRate_Setting
import Definitions.Def_PerturbSDE_StrongRate_Perturbation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- Hutzenthaler–Jentzen, arXiv:1401.0295v1, p. 13, Theorem 2.10, (43), finite-dimensional case
`H = ℝ^d`, `U = ℝ^m`: the perturbation estimate. If `X` solves `dX = µ(X) dt + σ(X) dW`,
`Y = Y_0 + ∫ a ds + ∫ b dW`, both `𝒪`-valued on `[0, T]`, `a, b, χ` predictable, and (42) holds, then
for all `r, q ∈ (0, ∞]` with `1/p + 1/q = 1/r`,
`‖X_τ − Y_τ‖_{L^r} ≤ ‖exp(∫_0^τ [ratio + χ_s]^+ ds)‖_{L^q}
  · [ (∫∫_{⟦0,τ⟧} p ‖X − Y‖^{p−2} [⟨X − Y, µ(Y) − a⟩ + ((p−1)(1+1/ε)/2) ‖b − σ(Y)‖² − χ ‖X − Y‖²]^+)^{1/p}
      + ‖X_0 − Y_0‖_{L^p} ]`, in `[0, ∞]`, for `ε ∈ [0, ∞]`. -/
theorem theorem_2_10 {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (T : ℝ≥0) (hT : 0 < T) (𝒪 : Set (SDEState d)) (h𝒪 : MeasurableSet 𝒪)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsWienerMartingale P ℱ W)
    (mu : SDEState d → SDEState d) (sigma : SDEState d → Diffusion d m)
    (hmu : Measurable mu) (hsigma : Measurable sigma)
    (ε : ℝ≥0∞) (p : ℝ) (hp : 2 ≤ p) (τ : Ω → ℝ≥0) (hτ : IsStopTime P ℱ T τ)
    (X Y : ℝ≥0 → Ω → SDEState d) (hX𝒪 : ∀ t ≤ T, ∀ ω, X t ω ∈ 𝒪)
    (hY𝒪 : ∀ t ≤ T, ∀ ω, Y t ω ∈ 𝒪)
    (a : ℝ≥0 → Ω → SDEState d) (b : ℝ≥0 → Ω → Diffusion d m) (χ : ℝ≥0 → Ω → ℝ)
    (ha : IsStronglyPredictable ℱ a) (hb : IsStronglyPredictable ℱ b)
    (hχ : IsStronglyPredictable ℱ χ)
    (hint : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖a s.toNNReal ω‖ₑ + ‖b s.toNNReal ω‖ₑ ^ 2 + ‖mu (X s.toNNReal ω)‖ₑ +
        ‖sigma (X s.toNNReal ω)‖ₑ ^ 2 + ‖mu (Y s.toNNReal ω)‖ₑ +
        ‖sigma (Y s.toNNReal ω)‖ₑ ^ 2) < ⊤)
    (hX : IsSolution P ℱ W T (X 0) (fun z => mu z.2) (fun z => sigma z.2) X)
    (hY : IsItoProcess P ℱ W T (Y 0) a b Y)
    (h42 : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) (τ ω),
      (monoRatio mu sigma p ε (X s.toNNReal ω) (Y s.toNNReal ω) +
        (χ s.toNNReal ω : EReal)).toENNReal < ⊤) :
    ∀ r q : ℝ≥0∞, r ≠ 0 → q ≠ 0 → (ENNReal.ofReal p)⁻¹ + q⁻¹ = r⁻¹ →
      eLpNorm (fun ω => X (τ ω) ω - Y (τ ω) ω) r P ≤
        eLpNorm (expPosIntegral
            (fun s ω => monoRatio mu sigma p ε (X s ω) (Y s ω) + (χ s ω : EReal)) τ) q P *
          ((∫⁻ z, localError mu sigma p ε X Y a b χ z.1.toNNReal z.2
                ∂(onStochInterval P τ)) ^ (1 / p) +
            eLpNorm (fun ω => X 0 ω - Y 0 ω) (ENNReal.ofReal p) P) := by sorry

end PerturbSDE.StrongRate
