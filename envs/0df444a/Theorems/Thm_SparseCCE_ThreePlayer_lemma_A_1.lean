-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_A_1
-- name    : SparseCCE.ThreePlayer.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:55.312953+00:00
-- url     : https://prove2.me/theorems/1ccbe7fc-1906-478d-911b-85c0356b2137
-- title:
--   Lemma A.1 — near causality suffices: $|E[F\mathbf 1_{S_H}]-\lambda_{>h}E[F\mathbf 1_{S_h}]|\le\delta_\pi$
-- statement:
--   Let $\Gamma$ be a repeated game, run the simulation with transcripts $z\sim\pi\in\Delta(Z)$, and let $\delta_\pi=\sum_j\mathrm{err}_j(\pi)$. For every $h\in\{0,\dots,H\}$ and every payoff $F$ with $|F|\le1$ determined by the first $h$ outcomes,
--   $$\big|E[F\mathbf 1_{S_H}]-\lambda_{>h}E[F\mathbf 1_{S_h}]\big|\le\delta_\pi.$$
--   In particular ($h=0$, $F=1$), the success probability $\tilde Q_\pi(\Omega)$ is within $\delta_\pi$ of $\lambda$.
--
--   Differences from the source:
--   - encoding: a repeated game Γ described in words (§3.2: nature and the players move in a fixed order, each player once, signals determined by earlier moves of the round) → RepeatedGame over a RoundProtocol with nonempty move sets, a fixed move order and availability, and nature kernels indexed by round and public history, satisfying WellFormed; reason: This retains the sequential protocol without imposing stationary independent nature moves; rounds are indexed 0, …, H−1
--   - encoding: E[F 1_{S_h}] for the round-by-round simulation → simPrefixExp: ∑_z π(z) ∑_{u ∈ O^h} nat(u) 1{every z_j begins with the query–answer pairs of u} F(u); reason: the simulation passes the first h rounds’ checks and produces u exactly in this event (p. 16), so the expectations coincide
--   - encoding: h ∈ {0, …, H}; F determined by the first h outcomes → h : Fin (H+1); F a function of the first h outcomes, applied at full length to the first h outcomes of the play; reason: same quantities
--   - generalization: the positive-horizon repeated games used in the paper → the identities also cover H = 0 and a finite player set that may be empty; reason: At H = 0 there is one empty play and transcript, λ = 1 and every causality error is zero; with no players the well-formed nature protocol is still a probability law. All source instances are retained
--   - generalization: the private signal determined by earlier moves of a round → the signal rule may additionally depend on the round and public history, while still ignoring later moves; reason: The history is already observed; the simulation identities use only that the signal is determined before the player acts. Taking the round protocol’s signal rule gives the source setting
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma A.1, p. 30.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame
import Definitions.Def_SparseCCE_ThreePlayer_Transcripts

namespace SparseCCE.ThreePlayer

open RepeatedGame

/-- **Lemma A.1 (Near causality suffices)**, p. 30: run the simulation with transcripts `z ∼ π`
and let `δ_π = ∑_j err_j(π)`. For any `h ∈ {0, …, H}` and any payoff `F ∈ [−1, 1]` determined by
the first `h` outcomes, `|E[F 1_{S_H}] − λ_{>h} E[F 1_{S_h}]| ≤ δ_π`. In particular (`h = 0`,
`F = 1`), the success probability `Q̃_π(Ω)` is within `δ_π` of `λ`. -/
theorem lemma_A_1 {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι)
    (hΓ : Γ.WellFormed) (π : Γ.TProfile → ℝ) (hπ : IsDist π) :
    (∀ (h : Fin (Γ.H + 1)) (F : (Fin h.val → Γ.P.Outcome) → ℝ), (∀ u, |F u| ≤ 1) →
      |Γ.simPrefixExp π (Fin.last Γ.H)
          (fun u => F (fun l => u (Fin.castLE (Nat.le_of_lt_succ h.isLt) l))) -
        Γ.lamAfter h.val * Γ.simPrefixExp π h F| ≤ Γ.deltaErr π) ∧
    |∑ ω, Γ.simLaw π ω - Γ.lamTot| ≤ Γ.deltaErr π := by sorry

end SparseCCE.ThreePlayer
