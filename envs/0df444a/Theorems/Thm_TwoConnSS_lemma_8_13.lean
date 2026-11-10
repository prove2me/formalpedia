-- Prove2me | Theorems.Thm_TwoConnSS_lemma_8_13
-- name    : TwoConnSS.lemma_8_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:24.468103+00:00
-- url     : https://prove2.me/theorems/55d877fd-32bf-45e0-adcb-1b993143ff38
-- title:
--   Lemma 8.13 — $\mathrm{cost}_B(S_0)\le \frac65 m_4+\frac{67}{50}m_{\ne4}$
-- statement:
--   Let $G$ be a structured graph and $S_0$ an initial cover of $G$. Then
--   $$\mathrm{cost}_B(S_0) \le \tfrac65 m_4 + \tfrac{67}{50} m_{\ne 4}.$$
--
--   This is the initial budget of Algorithm B: $1/5$ per 4-cycle edge and $17/50$ per other edge pay all assignment-B credits.
--
--   Differences from the source:
--   - reading: the initial cover → any S₀ with `IsInitialCover G S₀`; reason: the properties stated in §8.1
--   - reading: G a structured instance (the standing assumption of Section 8, p.32) → a hypothesis `Structured α η G` for 11/9 ≤ α < 5/4, 0 < η ≤ 1/100; reason: Section 8 fixes these parameters and works on structured graphs throughout (p.32: 'We henceforth use 11/9 ≤ α < 5/4')
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Lemma 8.13, p.38 (PDF p.39)

import Mathlib
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_costB
import Definitions.Def_TwoConnSS_KA

namespace TwoConnSS

/-- **Lemma 8.13: the initial assignment-B budget.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Lemma 8.13, p.38: "The initial cover
satisfies costB(S0) ≤ (6/5)m4 + (67/50)·m≠4."

For a structured graph `G` and an initial cover `S₀` of it,
`cost_B(S₀) ≤ (6/5)m₄ + (67/50)m_{≠4}`.

**Formalization Note.** "The initial cover" is any `S₀` with `IsInitialCover G S₀`. -/
theorem lemma_8_13 (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) {V : Type*} [Fintype V] (G : SimpleGraph V) (S₀ : Finset (Sym2 V))
    (hG : Structured α η G) (hS₀ : IsInitialCover G S₀) :
    costB S₀ ≤ 6 / 5 * (m4 S₀ : ℚ) + 67 / 50 * (mNe4 S₀ : ℚ) := by sorry

end TwoConnSS
