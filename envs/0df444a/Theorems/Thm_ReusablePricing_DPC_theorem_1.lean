-- Prove2me | Theorems.Thm_ReusablePricing_DPC_theorem_1
-- name    : ReusablePricing.DPC.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:35.516484+00:00
-- url     : https://prove2.me/theorems/6b01ecff-6172-4dee-a2be-1dc25d3a748a
-- title:
--   Theorem 1, p. 13 — L(DPC(ϵ)) ≤ M₁[ϵ/n̲ + (T/n)exp{−(ϵ−1)²/(36 min{maxᵢCᵢ, n})}]
-- statement:
--   This is the performance guarantee of the Deterministic Price Control in the basic reusable-resource model.
--
--   Fix the number $J$ of service types, the A5 constant $\Psi$ and the bound $R$ on the revenue rates. There is a constant $M_1 > 0$, depending only on $J$, $\Psi$ and $R$, with the following property. Take any instance with $J$ service types that satisfies the standing hypotheses of §3–§4 (any $I$, $T$, $n$, $A$, $C$, $\lambda_U$, revenue rates $r^t$ and DET solution $\lambda^D$, any A5 constants $\varphi_L, \varphi_U$, and $\underline n$ of display (2)). Then for every
--   $$\epsilon \in \Big(1,\ \min\big\{\min\{\varphi_L,\varphi_U\}\cdot\underline n,\ 6\cdot\min\{\max_i C_i, n\} + 1\big\}\Big],$$
--   the average loss of DPC($\epsilon$) satisfies
--   $$\mathcal L(DPC(\epsilon)) \le M_1\cdot\Big[\frac{\epsilon}{\underline n} + \frac{T}{n}\exp\Big\{-\frac{(\epsilon-1)^2}{36\cdot\min\{\max_i C_i, n\}}\Big\}\Big].$$
--
--   Along the scaling (1), with $\epsilon$ of order $\sqrt{\theta\log\theta}$, this gives the average loss $O(\theta^{-1/2}\log^{1/2}\theta)$.
--
--   **Formalization Note.** The paper says "there exists a constant $M_1 > 0$ such that for all $T$, $C$ and $n$", and its proof (ec8) builds $M_1$ from $J$, $\Psi$ and $r^u$ only, independent of $T, C, n$ and $\epsilon$. The statement therefore chooses $M_1$ after $J$, $\Psi$, $R$ and before the instance and $\epsilon$; with $M_1$ chosen after the instance the bound would be trivial. $R$ (A4's bound, $|r^t| \le R$) plays the role of $r^u$. The model is in demand rates, with turn-off as rate $0$, at most one arrival per period ($J\lambda_U \le 1$), and expected revenue $\mathbf E[\sum_t r^t(\lambda^t)]$; see the definition files.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), p. 13, Theorem 1 and (3)

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control

namespace ReusablePricing.DPC

open Finset

/-- Theorem 1 with display (3), p. 13: there is `M₁ > 0`, depending only on `J`, `Ψ` and the
revenue bound `R`, such that for every instance satisfying the standing hypotheses of §3–§4 and every
`ε ∈ (1, min{min{φ_L, φ_U} n̲, 6 min{max_i C_i, n} + 1}]`,
`L(DPC(ε)) ≤ M₁ [ε/n̲ + (T/n) exp{-(ε - 1)² / (36 min{max_i C_i, n})}]`. -/
theorem theorem_1 :
    ∀ (J : ℕ) (Ψ R : ℝ), ∃ M₁ : ℝ, 0 < M₁ ∧
      ∀ (P : Basic) (φL φU : ℝ) (nl : ℕ) (ε : ℝ),
        P.J = J → P.Standing φL φU Ψ R nl →
        1 < ε → ε ≤ min (min φL φU * nl) (6 * P.minCapN + 1) →
        P.loss ε nl ≤
          M₁ * (ε / nl + ((P.T : ℝ) / P.n) *
            Real.exp (-(ε - 1) ^ 2 / (36 * P.minCapN))) := by sorry

end ReusablePricing.DPC
