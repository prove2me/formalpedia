-- Prove2me | Theorems.Thm_TorchFire_TF_lemma_8_3
-- name    : TorchFire.TF.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:48:14.236123+00:00
-- url     : https://prove2.me/theorems/cd323170-bb8c-44de-9b7c-a9961d434010
-- title:
--   Lemma 8.3 — disabling label $\ell_i$ before the split changes $\mathbb E\,\mathrm{Tr}(Z\rho)$ by at most $2Q_{\mathrm{pre}}2^{-\lambda/2}$
-- statement:
--   Fix $i\in[N]$. Replace $\Gamma$ by $\Gamma^0_i$ (85) also before the split in the experiment of Definition 6.2, keeping the other oracles and honest issuance unchanged, and let $\tilde\rho_i$ be the resulting joint input state of the parties after challenge issuance and the experiment's abort checks ($\rho$ is the same state without the replacement). For every effect $0\preceq Z\preceq I$ on the joint input, possibly depending on the classical oracle functions and the public inputs,
--   $$\big|\mathbb E[\mathrm{Tr}(Z\rho)]-\mathbb E[\mathrm{Tr}(Z\tilde\rho_i)]\big|\le2Q_{\mathrm{pre}}2^{-\lambda/2}\quad(89),$$
--   where $Q_{\mathrm{pre}}$ is the pre-split query bound.
--
--   The challenge label is uniform and hidden during preparation, so disabling its affine access before the split costs little; this is what lets the anchor reduction of Lemma 8.4 run.
--
--   Differences from the source:
--   - reading: the interactive game SPLIT in prose (adaptive spark queries, a torch request at any one point) → normal form: v spark flames issued first, one measured request J between two stages of A_0, entangled quantum registers B_i, probability Tr(T_{m+1}(Z_1..Z_N)ρ); reason: paper.md decision 4; simulates every adversary of Definition 6.2 with the same winning probability and query count
--   - generalization: QPT adversaries → oracle algorithms with arbitrary finite workspace and unitaries; only the number of queries is bounded; reason: every QPT oracle algorithm is one with polynomially many queries (p.18); paper.md decision 2
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: probabilities over oracle sampling, algorithmic randomness and measurement outcomes → averages over the uniform finite oracle sample of Tr(Eρ) for the final cq-state, measurements deferred (Fact 3.1); reason: paper.md decision 6
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
--   - reading: "the experiment's abort checks" → setup abort and label collision (the ideal experiment of (62)); reason: the proof applies the collision check (p.72) and Theorem 8.6 uses the ideal experiment
--   - reading: Z depending on the classical oracle functions and public inputs → Z a function of the oracle sample and the challenge serials; reason: the public inputs are pk = R (a constant) and s_1, …, s_N (p.69)
--   - encoding: the pre-split query bound Q_pre → the two stages of A_0 make at most Q_pre queries in total; reason: normal form of decision 4
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 8.3, (89), p.71; (85) p.70

import Mathlib
import Definitions.Def_TorchFire_TF_splitWinProb

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- **Lemma 8.3**, (89), p.71 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). Fix `i ∈ [N]`. Replace `Γ` by `Γ⁰_i` (85) also before the split
in the experiment of Definition 6.2, keeping the other oracles and honest issuance unchanged, and let
`ρ̃_i` be the resulting joint input state after challenge issuance and the experiment's abort checks
(setup abort and label collision; `ρ` is the same without the replacement). For every effect
`0 ⪯ Z ⪯ I` on the joint input, possibly depending on the classical oracle functions and the public
inputs, `|E[Tr(Zρ)] − E[Tr(Zρ̃_i)]| ≤ 2 Q_pre 2^{−λ/2}`, with `Q_pre` the pre-split query bound. -/
theorem lemma_8_3 (lam R m N v : ℕ) (hlam : 2 ≤ lam) (A : SplitAdv lam R m N v) (Qpre : ℕ)
    (hA : A.PreBounded Qpre) (i : Fin N)
    (Z : Sample lam R → (Fin N → Serial lam) →
      Matrix ((j : Fin N) → A.B j × Flame lam) ((j : Fin N) → A.B j × Flame lam) ℂ)
    (hZ : ∀ ω ss', IsEffect (Z ω ss')) :
    |avg (Sample lam R) (fun ω => ∑ ss' : Fin N → Serial lam,
        accProb (Z ω ss') (splitRho A ω (pubOracle ω) ss' true)) -
      avg (Sample lam R) (fun ω => ∑ ss' : Fin N → Serial lam,
        accProb (Z ω ss') (splitRho A ω (modOracle ω (ss' i).1) ss' true))| ≤
      2 * Qpre * (2 : ℝ) ^ (-(lam : ℝ) / 2) := by sorry

end TorchFire.TF
