-- Prove2me | Theorems.Thm_WangZahlKakeya_assertion_E_implies_D_gain
-- name    : WangZahlKakeya.assertion_E_implies_D_gain
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T13:15:41.03938+00:00
-- url     : https://prove2.me/theorems/45131059-2f7f-4165-b7a7-036b13169eaf
-- title:
--   Induction on scales: $E(\sigma,\omega) \Rightarrow D(\sigma,\omega - g(\sigma,\omega))$ (Wang--Zahl, Proposition 1.7)
-- statement:
--   **The self-improvement step.**
--
--   There is a function $g : [0,2/3] \times (0,1] \to (0,1]$ such that for all $0 \le \sigma \le 2/3$ and $0 < \omega \le 1$,
--
--   $$E(\sigma,\omega) \;\Longrightarrow\; D\big(\sigma,\ \omega - g(\sigma,\omega)\big).$$
--
--   Since smaller $\omega$ is a stronger estimate, this says that assuming the volume estimate at parameters $(\sigma,\omega)$ yields a strictly better estimate, with a quantitative gain $g(\sigma,\omega) > 0$ depending only on $\sigma$ and $\omega$. Combined with the equivalence of $D$ and $E$, iterating this step drives $\omega$ — and, by trading the gain against the cardinality bound $\#\mathbb{T} \lesssim \delta^{-4}$, also $\sigma$ — down to $0$.
--
--   This is the technical heart of the paper: the proof applies the assumed estimate at many locations and scales, using a two-scale grains decomposition and a structure theorem for families of convex sets.
--
--   **Formalization Note** The gain function is asserted to exist as a function of two real variables that is positive and at most $1$ on the stated parameter range; its values outside that range are unconstrained. The statement is restricted to $\omega \le 1$, matching the domain $(0,1]$ of $g$ in the source.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 7, Proposition 1.7 (proved in §11)

import Definitions.Def_WangZahlKakeya_assertions

namespace WangZahlKakeya

theorem assertion_E_implies_D_gain :
    ∃ g : ℝ → ℝ → ℝ,
      (∀ σ ω : ℝ, 0 ≤ σ → σ ≤ 2 / 3 → 0 < ω → ω ≤ 1 → 0 < g σ ω ∧ g σ ω ≤ 1) ∧
      (∀ σ ω : ℝ, 0 ≤ σ → σ ≤ 2 / 3 → 0 < ω → ω ≤ 1 →
        AssertionE σ ω → AssertionD σ (ω - g σ ω)) := by sorry

end WangZahlKakeya
