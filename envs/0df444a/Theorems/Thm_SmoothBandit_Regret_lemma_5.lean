-- Prove2me | Theorems.Thm_SmoothBandit_Regret_lemma_5
-- name    : SmoothBandit.Regret.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:40.192389+00:00
-- url     : https://prove2.me/theorems/2e2ee44e-de3e-47ac-b6b1-925593c84e6f
-- title:
--   Lemma 5, p. 22 — on Ḡ_{k−1} ∩ M̄_{k−1}: ℛ_k ⊆ {|τ| ≤ 2ϵ_{k−1}}, ⋃ℰ_{a,j} ⊆ {aτ > 0}, 𝒬_a ⊆ ⋃ℰ_{a,j} ∪ ℛ_k, 𝒟_{a,k} ⊆ {aτ < 0}
-- statement:
--   There is $T_0$, depending only on the parameters, with the following property. Let
--
--   $$T \ge T_0 \vee \exp\Big(1 \vee \frac{C_0(2\beta+d)}{4(2r_0)^{2\beta}(2\beta+d+\beta d)}\Big),$$
--
--   and run Algorithm 1 with horizon $T$ on an instance whose regions $\mathcal Q_{\pm1}$ satisfy Assumption 2, whose support satisfies $\mathcal X \subseteq [0,1]^d$, and whose mean rewards take values in $[0,1]$ on $\mathcal X$. Fix $1 \le k \le K$. On the event $\bar{\mathcal G}_{k-1} \cap \bar{\mathcal M}_{k-1}$ (estimates accurate and samples plentiful in all earlier epochs), for $a = \pm1$:
--   1. $\mathcal R_k \cap \mathcal X \subseteq \{x \in \mathcal X : |\tau(x)| \le 2\epsilon_{k-1}\}$;
--   2. $(\bigcup_{j=1}^k\mathcal E_{a,j}) \cap \mathcal X \subseteq \{x \in \mathcal X : a\tau(x) > 0\}$;
--   3. $\mathcal Q_a \subseteq ((\bigcup_{j=1}^k\mathcal E_{a,j}) \cup \mathcal R_k) \cap \mathcal X$, for the points of $\mathcal Q_a$ lying in a cube of positive volume;
--   4. if moreover $\mathcal M_k$ holds, $\mathcal D_{a,k} \cap \mathcal X \subseteq \{x \in \mathcal X : a\tau(x) < 0\}$.
--
--   In words: the algorithm randomises only where the two arms are nearly tied, exploits an arm only where it is optimal, keeps collecting data for each arm wherever that arm is optimal, and hands an inestimable cube to the arm that is optimal there.
--
--   **Formalization Note.** $T_0$ is Lemma 3's; it is existential and chosen before the instance. Three departures from the page, each recorded in the mission notes. (a) Statement 4 is stated on $\bar{\mathcal G}_{k-1} \cap \bar{\mathcal M}_{k-1} \cap \mathcal M_k$: $\mathcal D_{a,k}$ is built with $H_{a,k}$, and the proof (p. 45) needs $H_{a,k} \le 2r_0$, which follows from $\mathcal M_k$ (Lemma 13) but not from the earlier events; without it statement 4 fails when epoch $k$ yields few samples of arm $a$. (b) Statement 3 excludes the points of $\mathcal Q_a$ in cubes of zero volume, which the rule $x \in G$ of (8)–(9) drops after the first epoch; they form a Lebesgue-null set (the page's remark that the cubes of $G$ cover $\mathcal X$, p. 16, holds only up to them). (c) $k \le K$, the range in which the regions are defined. The hypotheses $\mathcal X \subseteq [0,1]^d$ and $\eta_a \in [0,1]$ on $\mathcal X$ are parts of Assumption 3 and of the model the proof uses (statement 1 at $k = 1$ needs $|\tau| \le 2$).
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 22, Lemma 5 (proof pp. 44–45)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem lemma_5 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing) :
    ∃ T0 : ℝ, ∀ T : ℕ,
      max T0 (Real.exp (max 1 (C0 P d * (2 * P.β + d) /
        (4 * (2 * P.r0) ^ (2 * P.β) * (2 * P.β + d + P.β * d))))) ≤ T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω),
        M.𝒳 ⊆ cube d → (∀ a, ∀ x ∈ M.𝒳, M.η a x ∈ Set.Icc (0 : ℝ) 1) → Assumption2 P M →
        ∀ k : ℕ, 1 ≤ k → k ≤ numEpochs P d T →
        ∀ ω ∈ Gbar P T M (k - 1) ∩ Mbar P T M (k - 1), ∀ a : Arm,
          (∀ x ∈ M.𝒳, gIdx P d T x ∈ Rk P T M k ω → |tau M x| ≤ 2 * eps (k - 1)) ∧
          (∀ x ∈ M.𝒳, gIdx P d T x ∈ Ecum P T M a k ω → 0 < armSign a * tau M x) ∧
          (∀ x ∈ Q M a, gIdx P d T x ∈ Gset P T M → x ∈ suppK P T M a k ω) ∧
          (ω ∈ Mev P T M k →
            ∀ x ∈ M.𝒳, gIdx P d T x ∈ Dk P T M a k ω → armSign a * tau M x < 0) := by sorry

end SmoothBandit.Regret
