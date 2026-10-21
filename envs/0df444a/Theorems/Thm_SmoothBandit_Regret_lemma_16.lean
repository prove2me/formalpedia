-- Prove2me | Theorems.Thm_SmoothBandit_Regret_lemma_16
-- name    : SmoothBandit.Regret.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:38.985325+00:00
-- url     : https://prove2.me/theorems/70fea292-3540-4322-b00a-996eff7054ed
-- title:
--   Lemma 16, p. 37 — given Ḡ_{k−1}, M̄_{k−1}, N_{±1,k} = n_{±1,k}, the uniform CATE error exceeds ϵ_k w.p. ≤ δ^{−d}(8+4M_β²)exp(−C₀n^{2β/(2β+d)}ϵ_k²)
-- statement:
--   There is $T_0$, depending only on the parameters, with the following property. Let $T \ge T_0 \vee \exp\big(1 \vee \frac{C_0(2\beta+d)}{4(2r_0)^{2\beta}(2\beta+d+\beta d)}\big)$, take an instance satisfying Assumptions 1 to 3, and run Algorithm 1 with horizon $T$. Let $1 \le k \le K - 1$ and let $n_{1,k}, n_{-1,k}$ be integers with $n_{1,k} + n_{-1,k} = n_k$ and
--
--   $$n_{\pm1,k} \ge \Big(\frac{6\sqrt{M_\beta}\,L v_d\mu_{\max}}{p\lambda_0\epsilon_k}\Big)^{\frac{2\beta+d}{\beta}} .$$
--
--   Write $B = \bar{\mathcal G}_{k-1} \cap \bar{\mathcal M}_{k-1} \cap \{N_{1,k} = n_{1,k}\} \cap \{N_{-1,k} = n_{-1,k}\}$. Then the CATE estimate $\hat\tau_k$ built from the samples of epoch $k$ satisfies
--
--   $$P\Big(\sup_{x \in \mathcal R_k \cap \mathcal D^C_{1,k} \cap \mathcal D^C_{-1,k}} |\hat\tau_k(x) - \tau(x)| \ge \epsilon_k \,\Big|\, B\Big) \le \delta^{-d}(8 + 4M_\beta^2)\exp\big(-C_0\, (n_{1,k} \wedge n_{-1,k})^{\frac{2\beta}{2\beta+d}}\epsilon_k^2\big).$$
--
--   This is the uniform concentration of the local polynomial estimates under the adaptively collected samples, and the source of the first bound of Theorem 1.
--
--   **Formalization Note.** The conditional probability is written as $P(A \cap B) \le c\,P(B)$, which is the page's statement when $P(B) > 0$ and holds trivially otherwise. The page's exponent has $n_{a,k}$ with a free $a$; the proof of Theorem 1 (p. 49) uses $\min\{N_{1,k}, N_{-1,k}\}$, so the minimum is used. The page's "$6\sqrt M$" is $6\sqrt{M_\beta}$. The supremum is in the extended reals.
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 37, Lemma 16 (proof pp. 37–42)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem lemma_16 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing) :
    ∃ T0 : ℝ, ∀ T : ℕ,
      max T0 (Real.exp (max 1 (C0 P d * (2 * P.β + d) /
        (4 * (2 * P.r0) ^ (2 * P.β) * (2 * P.β + d + P.β * d))))) ≤ T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω),
        IsMachine M → Assumption1 P M → Assumption2 P M → Assumption3 P M →
        ∀ k : ℕ, 1 ≤ k → k ≤ numEpochs P d T - 1 →
        ∀ n1 n2 : ℕ,
          (6 * Real.sqrt (Mbeta d P.β) * P.L * vd d * P.muMax /
              (pConst P d * lam0 P d * eps k)) ^ ((2 * P.β + d) / P.β) ≤ (n1 : ℝ) →
          (6 * Real.sqrt (Mbeta d P.β) * P.L * vd d * P.muMax /
              (pConst P d * lam0 P d * eps k)) ^ ((2 * P.β + d) / P.β) ≤ (n2 : ℝ) →
          n1 + n2 = nEp P d T k →
          M.P ({ω | ((eps k : ℝ) : EReal) ≤ supErr P T M k ω} ∩
              (Gbar P T M (k - 1) ∩ Mbar P T M (k - 1) ∩
                {ω | Nk P T M true k ω = n1} ∩ {ω | Nk P T M false k ω = n2})) ≤
            ENNReal.ofReal ((delta P d T ^ d)⁻¹ * (8 + 4 * (Mbeta d P.β : ℝ) ^ 2) *
                Real.exp (-(C0 P d * ((min n1 n2 : ℕ) : ℝ) ^ (2 * P.β / (2 * P.β + d)) *
                  eps k ^ 2))) *
              M.P (Gbar P T M (k - 1) ∩ Mbar P T M (k - 1) ∩
                {ω | Nk P T M true k ω = n1} ∩ {ω | Nk P T M false k ω = n2}) := by sorry

end SmoothBandit.Regret
