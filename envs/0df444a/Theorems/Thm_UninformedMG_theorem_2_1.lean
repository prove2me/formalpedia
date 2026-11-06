-- Prove2me | Theorems.Thm_UninformedMG_theorem_2_1
-- name    : UninformedMG.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:06.371823+00:00
-- url     : https://prove2.me/theorems/a7e95d8d-f138-4abd-aa68-05291152e2ab
-- title:
--   Theorem 2.1 — with probability $1-\delta$, $\mathrm{Enr}_K\le H-1+2H\sqrt{2(A+1)SK\,C_\delta}$, and $\log N\le S\log(HK+1)$
-- statement:
--   Let $H\ge2$ and $K\ge1$. Consider any episodic two-player Markov game with $S$ nonterminal states, any $A$ with $|A_h|\le A$ for every step, the candidate grid $\mathcal V$ of Eq. (19) with $N=|\mathcal V|$, and $\delta\in(0,1)$. Let
--   $$C_\delta=(H+1)\log N+2S\log A+(H+1)\log(2/\delta),\qquad\lambda=\min\Big\{\big[2(A+1)S\big]^{-1},\sqrt{C_\delta/[2(A+1)SK]}\Big\}.$$
--   Against any adaptive opponent with adversarial initial states, every run of Algorithm 1 with this $\lambda$ satisfies, with probability at least $1-\delta$,
--   $$\mathrm{Enr}_K\le H-1+2H\sqrt{2(A+1)SK\,C_\delta},$$
--   and moreover $\log N\le S\log(HK+1)$. Together these give $\mathrm{Enr}_K=\widetilde O(H^{3/2}S\sqrt{AK})$ with probability at least $1-\delta$.
--
--   The guarantee is independent of the size of the opponent's action sets, although the opponent's actions are never observed. It is a worst-case $\widetilde O(\sqrt K)$ bound for the empirical Nash-value regret against arbitrary adaptive opponents.
--
--   Differences from the source:
--   - reading: Enr_K = Õ(H^{3/2} S √(AK)) with probability at least 1 − δ → P(Enr_K > H − 1 + 2H√(2(A+1)SK·C_δ)) ≤ δ, together with log N ≤ S log(HK + 1); reason: the explicit bound of the proof (p.26) is the strongest reading; with log N ≤ S log(HK+1) it implies the Õ statement
--   - generalization: A = |⋃_h A_h| → any A with |A_h| ≤ A for every step h; reason: the proof uses only |A_h| ≤ A (union bound over A^S policies, S log A, |A_h| ≤ A in Lemma B.6); the paper's A is one such bound
--   - generalization: the learner computes q^k from its own observations → any F^k-measurable selection q^k of the argmin in (23); reason: every learner selection is one
--   - encoding: the adaptive-opponent protocol of Section 1.1 → an Interaction: lexicographic history filtration, measurability of states, actions, policies, and the conditional step law; reason: this is the protocol's formal content; the natural history filtration is an instance
--   - encoding: with probability at least 1 − δ → the outer measure of the bad event is at most δ; reason: no measurability of the event is needed
--   - encoding: V^{μ,ν} as expected cumulative loss; D_{ℋres} the Bregman divergence of (20); z ∈ 𝒵 → V by the Bellman recursion; D by the formula of p.16; z as the pair (w, π); reason: the paper states the Bellman equation and the divergence formula; Eq. (4)
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Theorem 2.1, p.11 (PDF p.13), in the explicit form of its proof, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_enr
import Definitions.Def_UninformedMG_Run
import Definitions.Def_UninformedMG_cDelta
open MeasureTheory

namespace UninformedMG

/-- **Theorem 2.1** (p.11 = PDF p.13), in the explicit form derived in its proof (p.26 = PDF p.28).
Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

For `δ ∈ (0, 1)`, let `C_δ = (H + 1) log N + 2S log A + (H + 1) log(2/δ)` and
`λ = min{[2(A + 1)S]⁻¹, √(C_δ/[2(A + 1)SK])}`. Algorithm 1 ensures that with probability at least `1 − δ`,
`Enr_K ≤ H − 1 + 2H√(2(A + 1)SK C_δ)`; moreover `log N ≤ S log(HK + 1)` (Eq. (19)), so that
`Enr_K = Õ(H^{3/2} S √(AK))`.

**Formalization Note.** Every game with `H ≥ 2` steps (Section 2's standing assumption), `K ≥ 1`
episodes, every `A ≥ |A_h|`, every adaptive opponent and adversarial initial states (`Interaction`),
and every run of Algorithm 1 on the grid of Eq. (19) with the theorem's `λ` (`Run`). The bad event
`{Enr_K > H − 1 + 2H√(2(A+1)SK C_δ)}` has outer measure at most `δ`. `N = |V|`, `S` = `numStates`. -/
theorem theorem_2_1 {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Interaction G K Ω P)
    (R : Run (grid G K) (lamThm H K G.numStates (Fintype.card (grid G K).C) A δ) I) :
    P {ω | (H : ℝ) - 1 + 2 * H * Real.sqrt (2 * ((A : ℝ) + 1) * G.numStates * K *
          cDelta H G.numStates (Fintype.card (grid G K).C) A δ) <
        enr G (fun k => I.lpol k ω) (fun k => I.opol k ω) (fun k => I.st k 0 ω)} ≤
      ENNReal.ofReal δ ∧
    Real.log (Fintype.card (grid G K).C) ≤ (G.numStates : ℝ) * Real.log ((H : ℝ) * K + 1) := by sorry

end UninformedMG
