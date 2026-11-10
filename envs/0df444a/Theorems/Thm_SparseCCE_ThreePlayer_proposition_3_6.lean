-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_proposition_3_6
-- name    : SparseCCE.ThreePlayer.proposition_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:52.306564+00:00
-- url     : https://prove2.me/theorems/042ccf3d-0bac-42be-a18e-3f28c009dd27
-- title:
--   Proposition 3.6 — change of measure: $\tilde Q_\pi(\Omega)\in[\lambda/2,3\lambda/2]$ and $P\le 2CQ_x$
-- statement:
--   Let $\Gamma$ be a repeated game and $\pi\in\Delta(Z)$ with $\delta_\pi\le\lambda/2$ and $\pi\le C\bigotimes_jp_j$, where each $p_j\in\Delta(Z_j)$ represents a legal strategy $x_j$. Then $\lambda/2\le\tilde Q_\pi(\Omega)\le3\lambda/2$, and $P=\tilde Q_\pi/\tilde Q_\pi(\Omega)$ satisfies $P(\omega)\le2C\,Q_x(\omega)$ for every play $\omega$.
--
--   Differences from the source:
--   - encoding: a repeated game Γ described in words (§3.2: nature and the players move in a fixed order, each player once, signals determined by earlier moves of the round) → RepeatedGame over a RoundProtocol with nonempty move sets, a fixed move order and availability, and nature kernels indexed by round and public history, satisfying WellFormed; reason: This retains the sequential protocol without imposing stationary independent nature moves; rounds are indexed 0, …, H−1
--   - generalization: the positive-horizon repeated games used in the paper → the identities also cover H = 0 and a finite player set that may be empty; reason: At H = 0 there is one empty play and transcript, λ = 1 and every causality error is zero; with no players the well-formed nature protocol is still a probability law. All source instances are retained
--   - generalization: the private signal determined by earlier moves of a round → the signal rule may additionally depend on the round and public history, while still ignoring later moves; reason: The history is already observed; the simulation identities use only that the signal is determined before the player acts. Taking the round protocol’s signal rule gives the source setting
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Proposition 3.6, p. 17; proof App. A.3, p. 31.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame
import Definitions.Def_SparseCCE_ThreePlayer_Transcripts

namespace SparseCCE.ThreePlayer

open RepeatedGame

/-- **Proposition 3.6 (Change of measure)**, p. 17: let `π ∈ Δ(Z)` satisfy `δ_π ≤ λ/2` and
`π ≤ C ⊗_j p_j`, where each law `p_j` represents a legal strategy `x_j`. Then the success
probability `Q̃_π(Ω)` lies in `[λ/2, 3λ/2]`, and the law `P = Q̃_π / Q̃_π(Ω)` of the simulated play,
conditionally on success, satisfies `P ≤ 2C Q_x`. -/
theorem proposition_3_6 {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι)
    (hΓ : Γ.WellFormed) (π : Γ.TProfile → ℝ) (hπ : IsDist π) (C : ℝ)
    (p : (j : ι) → Γ.Transcript j → ℝ) (hp : ∀ j, IsDist (p j)) (x : Γ.StrategyProfile)
    (hx : ∀ j, Γ.IsLegal (x j)) (hrep : ∀ j, Γ.Represents (p j) (x j))
    (hδ : Γ.deltaErr π ≤ Γ.lamTot / 2) (hC : ∀ z, π z ≤ C * ∏ j, p j (z j)) :
    Γ.lamTot / 2 ≤ ∑ ω, Γ.simLaw π ω ∧ ∑ ω, Γ.simLaw π ω ≤ 3 * Γ.lamTot / 2 ∧
      ∀ ω, Γ.simLaw π ω / ∑ ω', Γ.simLaw π ω' ≤ 2 * C * Γ.lawOfPlay x ω := by sorry

end SparseCCE.ThreePlayer
