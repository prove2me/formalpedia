-- Prove2me | Theorems.Thm_StrategicRFx_Benefit_lemma_4
-- name    : StrategicRFx.Benefit.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:04.346593+00:00
-- url     : https://prove2.me/theorems/0ddb461a-e517-49ef-b483-92fb383adf54
-- title:
--   Lemma 4, p. 24 — leader's offer accepted at optimality: the profits, and the buyer accepts π̃_j iff π̃_j ≤ θ_j(Π − π̃_i − Π^{-j})^+
-- statement:
--   Let the offers $\tilde\pi_1,\tilde\pi_2\ge 0$ be given and suppose that, at optimality, the buyer first negotiates with supplier $i$ and accepts his offer $\tilde\pi_i$; let $(\pi_i,\pi_0^{-j})$ be the solution of [RFx-i] she reaches, and $j$ the other supplier. Then:
--
--   1. If the buyer accepts $\tilde\pi_j$, then $\pi_i=\tilde\pi_i$ and her profit is $\Pi-\tilde\pi_i-\tilde\pi_j$ (supplier $j$ receives $\tilde\pi_j$).
--   2. If she rejects $\tilde\pi_j$, supplier $j$ receives $\pi_j=\theta_j(\Pi-\pi_i-\Pi^{-j})^+$ and the buyer receives $\pi_0=\Pi-\pi_i-\pi_j$.
--   3. Accepting $\tilde\pi_j$ happens if and only if
--   $$\tilde\pi_j\le\theta_j\big(\Pi-\tilde\pi_i-\Pi^{-j}\big)^+ .$$
--
--   Together with Lemma 5 this lemma characterizes the buyer's response to a pair of offers and yields Lemma 2.
--
--   **Formalization Note** "At optimality" means: $(\pi_i,\pi_0^{-j})$ solves [RFx-i] for leader $i$ with the leader's offer accepted, and no other option (other leader, rejecting the leader's offer, any other solution) gives the buyer more. The buyer accepts $\tilde\pi_j$ when $\tilde\pi_j\le\pi_j(\pi_i,\pi_0^{-j})$ (ties: accept). Every solution of [RFx-i] is covered, including the degenerate case where the maximal Nash product is $0$. The lemma's piecewise closed form of $\pi_i$ and its "Moreover" sentence (continuity and monotonicity) are not formalized here.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), Lemma 4, p. 24 (proof pp. ec7–ec10)

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit

/-- Lemma 4 (p. 24), first, second (without the closed form of `π_i`) and last sentences.
Suppose that at optimality the buyer first accepts the offer `π̃_i` (`j = other i`).
If she accepts `π̃_j`, then `π_i = π̃_i` and her profit is `Π - π̃_i - π̃_j`; if she rejects `π̃_j`,
then `π_j = θ_j (Π - π_i - Π^{-j})^+` and her profit is `Π - π_i - π_j`; and accepting `π̃_j` is
optimal iff `π̃_j ≤ θ_j (Π - π̃_i - Π^{-j})^+`. -/
theorem lemma_4 (P : Params) (hP : Standing P) (t : Fin 2 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (i : Fin 2) (π π' : ℝ) (hopt : IsBuyerOptimal P t i true π π') :
    (AcceptsFollower P i t π π' →
      π = t i ∧ leaderBuyer P i t π π' = P.Pi - t i - t (other i)) ∧
    (¬ AcceptsFollower P i t π π' →
      followerSplit P (other i) π π' = P.θ (other i) * max (P.Pi - π - P.PiEx (other i)) 0 ∧
        leaderBuyer P i t π π' = P.Pi - π - followerSplit P (other i) π π') ∧
    (AcceptsFollower P i t π π' ↔
      t (other i) ≤ P.θ (other i) * max (P.Pi - t i - P.PiEx (other i)) 0) := by sorry

end StrategicRFx.Benefit
