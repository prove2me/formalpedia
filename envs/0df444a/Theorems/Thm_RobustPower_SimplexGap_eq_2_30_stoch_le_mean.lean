-- Prove2me | Theorems.Thm_RobustPower_SimplexGap_eq_2_30_stoch_le_mean
-- name    : RobustPower.SimplexGap.eq_2_30_stoch_le_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:29:11.898985+00:00
-- url     : https://prove2.me/theorems/b92ef211-764c-4384-9f0b-c70d482c41d1
-- title:
--   Eq. (2.30) — ŷ(ω) = b(ω) is feasible for Π_Stoch(b), so z_Stoch(b) ≤ E_µ[bₙ(ω)]
-- statement:
--   Consider the instance of Theorem 2.6: $n\ge 3$, $n_1=0$ ($A=0$, $c=0$), $n_2=m=n$, $B=I_n$, $d=e_n=(0,\dots,0,1)$, no integer coordinates, and a scenario model $(\Omega,\mu,b)$ in which $\mu$ is a probability measure, $b$ is measurable, $I_b(\Omega)=\Delta_n=\{b\ge 0:\sum_j b_j\le 1\}$, and $\mu$ is uniform on $\Delta_n$ (the law of $b$ is normalized Lebesgue measure on $\Delta_n$). Then
--
--   1. the policy $\hat y(\omega)=b(\omega)$ is feasible for the stochastic problem $\Pi_{\mathrm{Stoch}}(b)$ (it is integrable, nonnegative, and $I_n\hat y(\omega)=b(\omega)$ for every $\omega$);
--   2. consequently
--   $$z_{\mathrm{Stoch}}(b)\ \le\ \mathbb E_\mu[d^T\hat y(\omega)]=\mathbb E_\mu[\hat y_n(\omega)]=\mathbb E_\mu[b_n(\omega)].$$
--
--   This is the stochastic half of the proof of Theorem 2.6.
--
--   **Formalization Note** The $n$-th coordinate is index $n-1$ of `Fin n`. $z_{\mathrm{Stoch}}(b)$ is the `EReal` infimum of the `Problems` file over integrable policies satisfying the constraints in every scenario; the right-hand side is the real Bochner integral $\int b_n\,d\mu$ cast to `EReal`.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 20, proof of Theorem 2.6, Eq. (2.30)

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_Problems
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

namespace RobustPower.SimplexGap

open MeasureTheory

/-- Eq. (2.30): on the instance of Theorem 2.6, the policy `ŷ(ω) = b(ω)` is feasible for
`Π_Stoch(b)`, hence `z_Stoch(b) ≤ E_μ[dᵀŷ(ω)] = E_μ[bₙ(ω)]`. -/
theorem eq_2_30_stoch_le_mean (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → Fin n → ℝ)
    (hμb : IsUniformOnSimplex n μ b) :
    StochFeasible μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅
        (0 : Fin 0 → ℝ) b ∧
      zStoch μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin 0 → ℝ)
          (lastUnit n) b ∅ ∅ ≤ ((∫ ω, b ω ⟨n - 1, by omega⟩ ∂μ : ℝ) : EReal) := by sorry

end RobustPower.SimplexGap
