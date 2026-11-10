-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_A_2
-- name    : SparseCCE.ThreePlayer.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:07:00.314198+00:00
-- url     : https://prove2.me/theorems/a01e7325-2015-4442-9804-6a8e9320341b
-- title:
--   Lemma A.2 — the repaired law $p^c$ is causal and $\|p^c-p\|_1\le\mathrm{err}_j(p)$
-- statement:
--   Let $\Gamma$ be a repeated game, $j$ a player and $p\in\Delta(Z_j)$. Every repaired law $p^c(z)=\lambda_j\prod_hp(\alpha_h\mid v_h,q_h)$ of $p$ is causal and satisfies $\|p^c-p\|_1=\sum_z|p^c(z)-p(z)|\le\mathrm{err}_j(p)$.
--
--   Differences from the source:
--   - encoding: a repeated game Γ described in words (§3.2: nature and the players move in a fixed order, each player once, signals determined by earlier moves of the round) → RepeatedGame over a RoundProtocol with nonempty move sets, a fixed move order and availability, and nature kernels indexed by round and public history, satisfying WellFormed; reason: This retains the sequential protocol without imposing stationary independent nature moves; rounds are indexed 0, …, H−1
--   - generalization: the conditional answer law p(· | v_h, q_h), undefined when p(v_h, q_h) = 0 → IsRepair: any distribution at those pairs, the conditional answer law elsewhere; reason: covers every completion of the undefined conditional laws, so it specializes to the source’s p^c
--   - generalization: the positive-horizon repeated games used in the paper → the identities also cover H = 0 and a finite player set that may be empty; reason: At H = 0 there is one empty play and transcript, λ = 1 and every causality error is zero; with no players the well-formed nature protocol is still a probability law. All source instances are retained
--   - generalization: the private signal determined by earlier moves of a round → the signal rule may additionally depend on the round and public history, while still ignoring later moves; reason: The history is already observed; the simulation identities use only that the signal is determined before the player acts. Taking the round protocol’s signal rule gives the source setting
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma A.2, p. 30.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame
import Definitions.Def_SparseCCE_ThreePlayer_Transcripts

namespace SparseCCE.ThreePlayer

open RepeatedGame

/-- **Lemma A.2 (Repairing a law)**, p. 30: for `p ∈ Δ(Z_j)`, the law `p^c` that draws every query
uniformly and every answer from the conditional answer law of `p`,
`p^c(z) = λ_j ∏_h p(α_h | v_h, q_h)`, is causal and `‖p^c − p‖₁ ≤ err_j(p)`. -/
theorem lemma_A_2 {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι)
    (hΓ : Γ.WellFormed) (j : ι) (p pc : Γ.Transcript j → ℝ) (hp : IsDist p)
    (hpc : Γ.IsRepair p pc) :
    Γ.IsCausal pc ∧ ∑ z, |pc z - p z| ≤ Γ.errMarg p := by sorry

end SparseCCE.ThreePlayer
