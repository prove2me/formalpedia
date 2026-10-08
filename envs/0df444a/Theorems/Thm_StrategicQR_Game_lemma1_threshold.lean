-- Prove2me | Theorems.Thm_StrategicQR_Game_lemma1_threshold
-- name    : StrategicQR.Game.lemma1_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:24:33.33662+00:00
-- url     : https://prove2.me/theorems/adf1f83b-b002-4a71-8124-3b0ea2df706b
-- title:
--   Lemma 1, p. 10 — strategic consumers follow a threshold rule $v^*\in[\underline v,\bar v]$
-- statement:
--   Let $\mu$ be a finite measure on $\mathbb R$ carried by $[0,p]$: the law of the sale price on the event that a waiting consumer receives a unit. A strategic consumer with second-period value $w$ who waits has expected surplus
--   $$\psi(w)=\int (w-s)^+\,d\mu(s),$$
--   and buying at the full price gives $v_M-p$. Then there is a threshold $v^*\in[\underline v,\bar v]$ such that
--
--   1. every value $w\in[\underline v,v^*)$ weakly prefers to buy in the first period: $\psi(w)\le v_M-p$;
--   2. every value $w\in(v^*,\bar v]$ weakly prefers to wait: $\psi(w)\ge v_M-p$;
--   3. if $\underline v<v^*<\bar v$, the consumer with value $v^*$ is indifferent: $\psi(v^*)=v_M-p$.
--
--   This is the threshold structure that reduces the strategic consumers' decisions to a single number $v^*$, the basis of the equilibrium definition.
--
--   **Formalization Note** The appendix proof works with a density $h(s)$ of the sale price. The sale price has atoms (at $s_l$ with probability $F(D_l)$, at $s_m$ with positive probability), so a general finite measure $\mu$ replaces $h$. The paper's last sentence ("a consumer with value $v^*$ is indifferent") holds only for an interior threshold: if every value strictly prefers to buy early, $v^*=\bar v$ and nobody is indifferent; this is the corrected form. Preferences are weak at the boundary because ties are allowed.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 10, Lemma 1; Technical Appendix p. 1 (PDF 33), proof of Lemma 1

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

open MeasureTheory

/-- Lemma 1 (Cachon–Swinney, p. 10; proof on Technical Appendix p. 1), the threshold structure
of strategic consumers' purchase timing. Let `μ` be any finite measure carried by the admissible
sale prices `[0, p]` (the law of the sale price on the event that the consumer receives a unit).
The waiting surplus of a consumer with second-period value `w` is `ψ(w) = ∫ (w - s)⁺ dμ(s)`.
There is a threshold `v* ∈ [v̲, v̄]` such that every value `w ∈ [v̲, v*)` weakly prefers buying
at `p` (`ψ(w) ≤ vM - p`), every value `w ∈ (v*, v̄]` weakly prefers waiting
(`ψ(w) ≥ vM - p`), and an interior threshold consumer is indifferent (`ψ(v*) = vM - p`). -/
theorem lemma1_threshold (M : Model) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc 0 M.p)ᶜ = 0) :
    ∃ v ∈ Set.Icc M.vlo M.vhi,
      (∀ w ∈ Set.Ico M.vlo v, ∫ s, max (w - s) 0 ∂μ ≤ M.vM - M.p) ∧
      (∀ w ∈ Set.Ioc v M.vhi, M.vM - M.p ≤ ∫ s, max (w - s) 0 ∂μ) ∧
      (M.vlo < v → v < M.vhi → ∫ s, max (v - s) 0 ∂μ = M.vM - M.p) := by sorry

end StrategicQR.Game
