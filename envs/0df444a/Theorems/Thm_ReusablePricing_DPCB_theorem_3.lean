-- Prove2me | Theorems.Thm_ReusablePricing_DPCB_theorem_3
-- name    : ReusablePricing.DPCB.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:08.509262+00:00
-- url     : https://prove2.me/theorems/d31d5fc1-44cc-4963-b587-ac4990f5b791
-- title:
--   Theorem 3, pp. 19–20 — L(DPC-B(m, ϵ)) ≤ M₃ Σ_k [ϵ_k/n̲_k + 1/m_k + (T/m_k) exp{−(min_k ϵ_k − 1)²/(256K² min{maxᵢCᵢ, m_k})}]
-- statement:
--   This is the main result of Lei and Jasin for the general setting with heterogeneous service times and advance reservation.
--
--   Fix the number of service types $K$, the constant $\Psi$ of Assumption A5 and a bound $R$ on the revenue rates. There is a constant $M_3 > 0$, depending only on $K$, $\Psi$ and $R$, with the following property. Take any instance of Section 6 satisfying the standing hypotheses (model facts, $\lambda^D$ optimal for DET-H, A4 with bound $R$, A5 with constants $\varphi_L, \varphi_U, \Psi$, and $\underline{n}_k$ the minimum count of p. 18), any valid batch partition with $1 \le m_k \le \underline{n}_k$, and buffers
--   $$
--   \epsilon_k \in \Bigl(1,\ \min\Bigl\{ \underline{n}_k \min\Bigl\{1, \frac{1 + 4 m_k \min\{\varphi_L,\varphi_U\}}{4m_k + \underline{n}_k}\Bigr\},\ 1 + 16\min\{\max_i C_i, m_k\} \Bigr\}\Bigr] .
--   $$
--   Then the average loss of DPC-B$(m,\epsilon)$ satisfies
--   $$
--   \mathcal{L}(\text{DPC-B}(m,\epsilon)) \le M_3 \sum_{k=1}^K \Bigl[ \frac{\epsilon_k}{\underline{n}_k} + \frac{1}{m_k} + \frac{T}{m_k} \exp\Bigl\{ -\frac{(\min_j \epsilon_j - 1)^2}{256 K^2 \min\{\max_i C_i, m_k\}} \Bigr\} \Bigr].
--   $$
--
--   Choosing $\epsilon_k$ of order $\sqrt{\underline{n}_k^c \log \underline{n}_k}$ and $m_k \approx \underline{n}_k^c$ along the scaling (7) turns this into the rate $O(\theta^{c/2-1}\log^{1/2}\theta + \theta^{-c})$ of display (9), which is $O(\theta^{-2/3}\log^{1/2}\theta)$ for $c = 2/3$.
--
--   **Formalization Note** $M_3$ is chosen before the instance: it may depend on $K$, $\Psi$ and $R$ only, and not on $T$, $C$, $n_k$, $\ell_k$, $m_k$, $\epsilon_k$, $\varphi_L$, $\varphi_U$ or the revenue functions (the proof on ec13 says "independent of $T$, $C$, $n_k$, $m_k \le \underline{n}_k$, and $\epsilon_k$"). Choosing it after the instance would make the bound trivial, since the loss is at most $2R$. In the exponent, $\min_j \epsilon_j$ is the minimum over all types (the page reuses the summation letter). The revenue bound $R$ replaces the proofs' $r^u$. The standing hypotheses, conventions and turn-off encoding are those of the definition files.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), pp. 19–20, Theorem 3 and display (8); proof in §EC.4, pp. ec8–ec13

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Control

open Finset

namespace ReusablePricing.DPCB

open General

/-- Theorem 3 (pp. 19–20, display (8)): there is `M₃ > 0`, depending only on `K`, `Ψ` and the
revenue bound `R`, such that for every instance of §6 satisfying the standing hypotheses, every
valid batch partition and every `m`, `ϵ` in the stated range,
`L(DPC-B(m, ϵ)) ≤ M₃ ∑_k [ϵ_k/n̲_k + 1/m_k + (T/m_k) exp{-(min_j ϵ_j - 1)² / (256 K² min{max_i C_i, m_k})}]`. -/
theorem theorem_3 :
    ∀ (K : ℕ) (Ψ R : ℝ), ∃ M₃ : ℝ, 0 < M₃ ∧
      ∀ (P : General) (φL φU : ℝ) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ)
        (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ),
        P.K = K →
        P.Standing R Ψ φL φU nl →
        P.BatchesValid m β B →
        (∀ k, 1 ≤ m k ∧ m k ≤ nl k) →
        (∀ k, 1 < ε k ∧
          ε k ≤ min ((nl k : ℝ) * min 1 ((1 + 4 * (m k : ℝ) * min φL φU) / (4 * (m k : ℝ) + (nl k : ℝ))))
                    (1 + 16 * min P.maxC (m k : ℝ))) →
        P.lossB nl m ε β ≤
          M₃ * ∑ k, (ε k / (nl k : ℝ) + 1 / (m k : ℝ) +
            (P.T : ℝ) / (m k : ℝ) *
              Real.exp (-(P.epsMin ε - 1) ^ 2 / (256 * (K : ℝ) ^ 2 * min P.maxC (m k : ℝ)))) := by sorry

end ReusablePricing.DPCB
