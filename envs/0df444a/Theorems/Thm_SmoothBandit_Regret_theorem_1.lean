-- Prove2me | Theorems.Thm_SmoothBandit_Regret_theorem_1
-- name    : SmoothBandit.Regret.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:35.18642+00:00
-- url     : https://prove2.me/theorems/a86562ee-c9c1-4eb4-ae9c-1f63e841ad60
-- title:
--   Theorem 1, p. 25 — ℙ(𝒢^C_k | Ḡ_{k−1}, M̄_k) ≤ (8+4M_β²)/T, ℙ(ℳ^C_k | Ḡ_{k−1}, M̄_{k−1}) ≤ 2/T, ℙ(Ḡ^C_k ∪ M̄^C_k) ≤ (10+4M_β²)k/T
-- statement:
--   There is $T_0$, depending only on the parameters, with the following property. Let
--
--   $$T \ge T_0 \vee \exp\Big(1 \vee \frac{C_0(2\beta+d)}{4(2r_0)^{2\beta}(2\beta+d+\beta d)} \vee \frac{36M_\beta L^2v_d^2\mu_{\max}^2C_0(2\beta+d)}{p^2\lambda_0^2(2\beta+d+\beta d)}\Big),$$
--
--   take an instance satisfying Assumptions 1 to 3, and run Algorithm 1 with horizon $T$. Then for every epoch $1 \le k \le K - 1$:
--   1. $P(\mathcal G^C_k \mid \bar{\mathcal G}_{k-1}, \bar{\mathcal M}_k) \le (8 + 4M_\beta^2)/T$;
--   2. $P(\mathcal M^C_k \mid \bar{\mathcal G}_{k-1}, \bar{\mathcal M}_{k-1}) \le 2/T$;
--   3. $P(\bar{\mathcal G}^C_k \cup \bar{\mathcal M}^C_k) \le (10 + 4M_\beta^2)k/T$.
--
--   The probability that the estimates fail or the samples run short before epoch $k$ is therefore of order $k/T$, which makes the second sum of the regret decomposition (13) of order $\log^2 T$.
--
--   **Formalization Note.** Each conditional probability $P(A \mid B) \le c$ is written as $P(A \cap B) \le c\,P(B)$, the page's statement when $P(B) > 0$. $T_0$ is Lemma 3's and is existential, chosen before the instance.
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 25, Theorem 1 (proof pp. 49–50)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem theorem_1 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing) :
    ∃ T0 : ℝ, ∀ T : ℕ,
      max T0 (Real.exp (max 1 (max
        (C0 P d * (2 * P.β + d) / (4 * (2 * P.r0) ^ (2 * P.β) * (2 * P.β + d + P.β * d)))
        (36 * (Mbeta d P.β : ℝ) * P.L ^ 2 * vd d ^ 2 * P.muMax ^ 2 * C0 P d * (2 * P.β + d) /
          (pConst P d ^ 2 * lam0 P d ^ 2 * (2 * P.β + d + P.β * d)))))) ≤ T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω),
        IsMachine M → Assumption1 P M → Assumption2 P M → Assumption3 P M →
        ∀ k : ℕ, 1 ≤ k → k ≤ numEpochs P d T - 1 →
          M.P ((Gev P T M k)ᶜ ∩ (Gbar P T M (k - 1) ∩ Mbar P T M k)) ≤
              ENNReal.ofReal ((8 + 4 * (Mbeta d P.β : ℝ) ^ 2) / T) *
                M.P (Gbar P T M (k - 1) ∩ Mbar P T M k) ∧
          M.P ((Mev P T M k)ᶜ ∩ (Gbar P T M (k - 1) ∩ Mbar P T M (k - 1))) ≤
              ENNReal.ofReal (2 / T) * M.P (Gbar P T M (k - 1) ∩ Mbar P T M (k - 1)) ∧
          M.P ((Gbar P T M k)ᶜ ∪ (Mbar P T M k)ᶜ) ≤
              ENNReal.ofReal ((10 + 4 * (Mbeta d P.β : ℝ) ^ 2) * k / T) := by sorry

end SmoothBandit.Regret
