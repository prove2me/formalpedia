-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_3_8
-- name    : SparseCCE.ThreePlayer.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:09:51.213397+00:00
-- url     : https://prove2.me/theorems/269ad6d1-a82a-427b-8167-d6108b551e43
-- title:
--   Lemma 3.8 — audits enforce causality: $\mathrm{err}_i(\nu_{ik})\le\delta$ in every $\varepsilon$-CCE
-- statement:
--   Let $G$ be a valid two-player two-action Bayesian game, $H$ a horizon, $\varepsilon_0\in(0,1)$, and consider the normal-form encoding of the kibitzer game with audits, $\varepsilon=\lambda\varepsilon_0/64$, $\delta=\lambda/(4M^3)$, $W=6HM^2/\delta$. If $\mu$ is an $\varepsilon$-CCE of this game (utilities $R_j$), then $\mathrm{err}_i(\nu_{ik})\le\delta$ for all players $i\ne k$.
--
--   Differences from the source:
--   - generalization: ε0 the constant of Lemma 3.1(a) → every real ε0 ∈ (0, 1); reason: the proof uses only ε ≤ 1; the source’s constant is one such value
--   - encoding: the type sets of G (nonempty because the marginals are positive) → instance arguments NeZero (G.n 0), NeZero (G.n 1); reason: implied by validity; needed only to make the kibitzer signal map total
--   - generalization: the kibitzer game with a positive horizon → H may also be zero; reason: At H = 0 the pure-strategy listing is empty and the deviation condition is vacuous in Lemma 3.7; in Lemma 3.8 there are no tests, so the conclusion is 0 ≤ 1/4. Positive horizons specialize to the source
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 3.8, p. 18; proof App. A.4, p. 31.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_BayesGame
import Definitions.Def_SparseCCE_ThreePlayer_Kibitzer
import Definitions.Def_SparseCCE_ThreePlayer_AuditedGame

namespace SparseCCE.ThreePlayer

/-- **Lemma 3.8 (Audits enforce causality)**, p. 18: if `μ` is an `ε`-CCE of the normal-form
encoding of the kibitzer game with audits (`ε = λε₀/64`, `δ = λ/(4M³)`, `W = 6HM²/δ`), then
`err_i(ν_{ik}) ≤ δ` for all players `i ≠ k`. -/
theorem lemma_3_8 (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (hG : G.Valid) (H : ℕ)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀ ∧ ε₀ < 1) (μ : ((j : Fin 3) → AAction G H j) → ℝ)
    (hμ : IsEpsCCE (auditUtil G H) μ (auditEps G H ε₀)) :
    ∀ i k : Fin 3, i ≠ k → (kGame G H).err ((kGame G H).recPairLaw (aTr G H) μ i k) ≤
      auditDelta G H := by sorry

end SparseCCE.ThreePlayer
