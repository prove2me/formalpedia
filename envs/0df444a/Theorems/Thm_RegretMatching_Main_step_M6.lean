-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M6
-- name    : RegretMatching.Main.step_M6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:34.792002+00:00
-- url     : https://prove2.me/theorems/f4f31d1c-d98c-480e-b26c-78470a47e5d1
-- title:
--   Step M6, Appendix, p. 1145 — α̂_{t,w}(j,s⁻ⁱ) = P[ŝ⁻ⁱ_{t+w} = s⁻ⁱ | h_t] [Π_t^{w+1} − Π_t^w](sⁱ_t, j)
-- statement:
--   For player $i$, positive integers $t,w$, a history $h_t$, $j\in S^i$ and $s^{-i}\in S^{-i}$,
--   $$\hat\alpha_{t,w}(j,s^{-i})=P[\hat s^{-i}_{t+w}=s^{-i}\mid h_t]\;\big[\Pi_t^{w+1}-\Pi_t^{w}\big](s^i_t,j),$$
--   where $\Pi_t^w$ is the $w$-th power of player $i$'s matrix $\Pi_t$ and $[\cdot](s^i_t,j)$ denotes the $(s^i_t,j)$ entry.
--
--   In the $\hat s$-process the other players' moves are independent of player $i$'s, so they factor out of $\hat\alpha$, and what remains is a difference of consecutive powers of a single stochastic matrix.
--
--   **Formalization Note.** $P[\hat s^{-i}_{t+w}=s^{-i}\mid h_t]$ is written $\sum_{k\in S^i}P[\hat s_{t+w}=(k,s^{-i})\mid h_t]$. The identity is a statement about the explicit $\hat s$-probabilities and needs no play.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1145, Appendix, Step M6; proof pp. 1147–1148

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M6
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) (t w : ℕ) (ht : 1 ≤ t) (hw : 1 ≤ w) (h : Fin t → (∀ i, S i)) (j : S i)
    (s : ∀ i, S i) :
    alphaHat u μ h (h ⟨t - 1, by omega⟩) i w j s
      = (∑ k : S i, shatProb u μ h (h ⟨t - 1, by omega⟩) w (Function.update s i k))
        * ((PiMat u μ h i ^ (w + 1) - PiMat u μ h i ^ w) (h ⟨t - 1, by omega⟩ i) j) := by sorry

end RegretMatching.Main
