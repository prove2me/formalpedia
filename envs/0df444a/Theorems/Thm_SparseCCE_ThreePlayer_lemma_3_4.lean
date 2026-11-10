-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_3_4
-- name    : SparseCCE.ThreePlayer.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:51.828667+00:00
-- url     : https://prove2.me/theorems/55fec7da-849a-4388-b3c9-8a4db79a0b3d
-- title:
--   Lemma 3.4 — faithful simulation: causal laws represent their decodings, and $\tilde Q_{\otimes_jp_j}=\lambda Q_x$
-- statement:
--   Let $\Gamma$ be a repeated game. (a) Every causal law $p\in\Delta(Z_j)$ represents every decoding of $p$, and $\mathrm{enc}(x_j)$ represents every legal strategy $x_j$. (b) If $p_j\in\Delta(Z_j)$ represents the legal strategy $x_j$ for every player $j$, then $\tilde Q_{\otimes_jp_j}(\omega)=\lambda\,Q_x(\omega)$ for every play $\omega$, and the success probability $\sum_\omega\tilde Q_{\otimes_jp_j}(\omega)$ equals $\lambda$.
--
--   Differences from the source:
--   - encoding: a repeated game Γ described in words (§3.2: nature and the players move in a fixed order, each player once, signals determined by earlier moves of the round) → RepeatedGame over a RoundProtocol with nonempty move sets, a fixed move order and availability, and nature kernels indexed by round and public history, satisfying WellFormed; reason: This retains the sequential protocol without imposing stationary independent nature moves; rounds are indexed 0, …, H−1
--   - generalization: the decoding of p, arbitrary at probability-zero prefix–query pairs → every legal strategy that agrees with the conditional answer law of p wherever the prefix and query have positive probability; reason: covers every choice the source allows, so it specializes to the source’s decoding
--   - encoding: causal: every round-h query uniform on Q_{j,h} and independent of the prefix → E_p[f_κ] = 0 for every test κ of j; reason: the source states this equivalence on p. 17
--   - encoding: the simulated law and the simulation with transcripts → the closed form Q̃_π(ω) = nat(ω) π(z(ω)) of eq. (3); reason: the source derives this form on p. 16 and takes it as the definition of Q̃_π
--   - encoding: "In other words, … succeeds with probability exactly λ" → the additional conjunct ∑_ω Q̃_{⊗p_j}(ω) = λ; reason: the paraphrase the statement itself gives
--   - generalization: the positive-horizon repeated games used in the paper → the identities also cover H = 0 and a finite player set that may be empty; reason: At H = 0 there is one empty play and transcript, λ = 1 and every causality error is zero; with no players the well-formed nature protocol is still a probability law. All source instances are retained
--   - generalization: the private signal determined by earlier moves of a round → the signal rule may additionally depend on the round and public history, while still ignoring later moves; reason: The history is already observed; the simulation identities use only that the signal is determined before the player acts. Taking the round protocol’s signal rule gives the source setting
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 3.4, p. 16; proof App. A.3, p. 29.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame
import Definitions.Def_SparseCCE_ThreePlayer_Transcripts

namespace SparseCCE.ThreePlayer

open RepeatedGame

/-- **Lemma 3.4 (Faithful simulation)**, p. 16: (a) every causal law represents its decoding, and
`enc(x_j)` represents `x_j`; (b) if `p_j` represents `x_j` for every player `j`, then
`Q̃_{⊗_j p_j} = λ Q_x`: with independent transcripts drawn from the laws `p_j`, the simulation
succeeds with probability exactly `λ`. -/
theorem lemma_3_4 {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι)
    (hΓ : Γ.WellFormed) :
    (∀ (j : ι) (p : Γ.Transcript j → ℝ) (x : Γ.Strategy j),
      IsDist p → Γ.IsCausal p → Γ.IsDecoding p x → Γ.Represents p x) ∧
    (∀ (j : ι) (x : Γ.Strategy j), Γ.IsLegal x → Γ.Represents (Γ.encLaw x) x) ∧
    (∀ (p : (j : ι) → Γ.Transcript j → ℝ) (x : Γ.StrategyProfile),
      (∀ j, IsDist (p j)) → (∀ j, Γ.IsLegal (x j)) → (∀ j, Γ.Represents (p j) (x j)) →
      (∀ ω, Γ.simLaw (fun z => ∏ j, p j (z j)) ω = Γ.lamTot * Γ.lawOfPlay x ω) ∧
      ∑ ω, Γ.simLaw (fun z => ∏ j, p j (z j)) ω = Γ.lamTot) := by sorry

end SparseCCE.ThreePlayer
