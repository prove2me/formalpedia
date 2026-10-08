-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M2
-- name    : RegretMatching.Main.step_M2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:37.139006+00:00
-- url     : https://prove2.me/theorems/8b6a64a1-0bb1-4ae8-8d00-0ce8b0102a50
-- title:
--   Step M2, Appendix, p. 1144 — R_t·E[A_{t+w}|h_t] = μ Σ_{s⁻ⁱ} Σ_j α_{t,w}(j,s⁻ⁱ) uⁱ(j,s⁻ⁱ)
-- statement:
--   Under regret matching (2.2) with footnote 5's $\mu$, fix a player $i$, positive integers $t,w$ and a history $h_t$ of positive probability. Then
--   $$R_t\cdot E[A_{t+w}\mid h_t]=\mu\sum_{s^{-i}\in S^{-i}}\sum_{j\in S^i}\alpha_{t,w}(j,s^{-i})\,u^i(j,s^{-i}),$$
--   where $\alpha_{t,w}(j,s^{-i})=\sum_{k\in S^i}\Pi_t(k,j)P[s_{t+w}=(k,s^{-i})\mid h_t]-P[s_{t+w}=(j,s^{-i})\mid h_t]$.
--
--   The identity rewrites the cross term of Step M1 through the transition probabilities of period $t$.
--
--   **Formalization Note.** The double sum over $s^{-i}\in S^{-i}$ and $j\in S^i$ is written as one sum over $s\in S$ with $j=s^i$, using $S\cong S^i\times S^{-i}$; `alpha` ignores the $i$-th coordinate of its profile argument and $u^i(s^i,s^{-i})=u^i(s)$.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1144, Appendix, definition of α_{t,w} and Step M2; proof p. 1146

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M2
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (p₁ : ∀ i, S i → ℝ) (hp₁ : ∀ i, p₁ i ∈ stdSimplex ℝ (S i))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → (∀ i, S i)) (hplay : IsPlay (rmMixed u μ p₁) P play)
    (i : ι) (t w : ℕ) (ht : 1 ≤ t) (hw : 1 ≤ w) (h : Fin t → (∀ i, S i))
    (hh : P {ω | hist play t ω = h} ≠ 0) :
    ∑ p ∈ (Finset.univ : Finset (S i)).offDiag,
        regretR u h i p.1 p.2 *
          condExpHist P play h (fun ω => regretA u i (play (t + w - 1) ω) p.1 p.2)
      = μ * ∑ s : (∀ i, S i), alpha u μ P play h i w (s i) s * u i s := by sorry

end RegretMatching.Main
