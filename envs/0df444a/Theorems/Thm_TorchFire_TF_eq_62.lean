-- Prove2me | Theorems.Thm_TorchFire_TF_eq_62
-- name    : TorchFire.TF.eq_62
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:47:49.070494+00:00
-- url     : https://prove2.me/theorems/3299e3a3-5282-4aff-bc9d-4792c7277818
-- title:
--   (62) — distinct labels: $p_{\mathrm{real}}\le p_{\mathrm{ideal}}+\binom{v+N}2 2^{-\lambda}$
-- statement:
--   Define the ideal experiment of the global non-proliferation game by additionally declaring failure if any two labels $\ell$ among the $v$ pre-split and $N$ challenge spark queries coincide. If $p_{\mathrm{real}}$ and $p_{\mathrm{ideal}}$ are the real and ideal winning probabilities of an adversary, then
--   $$p_{\mathrm{real}}\le p_{\mathrm{ideal}}+\binom{v+N}2 2^{-\lambda}=p_{\mathrm{ideal}}+\mathrm{negl}(\lambda)\quad(62)$$
--   for polynomial $v(\lambda),N(\lambda)$.
--
--   Differences from the source:
--   - reading: the interactive game SPLIT in prose (adaptive spark queries, a torch request at any one point) → normal form: v spark flames issued first, one measured request J between two stages of A_0, entangled quantum registers B_i, probability Tr(T_{m+1}(Z_1..Z_N)ρ); reason: paper.md decision 4; simulates every adversary of Definition 6.2 with the same winning probability and query count
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: probabilities over oracle sampling, algorithmic randomness and measurement outcomes → averages over the uniform finite oracle sample of Tr(Eρ) for the final cq-state, measurements deferred (Fact 3.1); reason: paper.md decision 6
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §8, (62), p.58

import Mathlib
import Definitions.Def_TorchFire_TF_splitWinProb
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS PPADSIS.SubexpSIS

namespace TorchFire.TF

/-- **Distinct labels, (62)**, §8, p.58 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593). Let the ideal experiment additionally declare failure
if two of the labels `ℓ` of the `v` pre-split and `N` challenge spark queries coincide. For every
adversary, `p_real ≤ p_ideal + (v + N choose 2) 2^{−λ}`, and the correction is negligible for
polynomially bounded `v(λ), N(λ)`. -/
theorem eq_62 :
    (∀ (lam R m N v : ℕ) (A : SplitAdv lam R m N v), 2 ≤ lam →
      splitWinProb A ≤ splitWinProbIdeal A + ((v + N).choose 2 : ℝ) * (2 : ℝ)⁻¹ ^ lam) ∧
    ∀ v N : ℕ → ℕ, PolyBounded v → PolyBounded N →
      Negligible fun lam => ((v lam + N lam).choose 2 : ℝ) * (2 : ℝ)⁻¹ ^ lam := by sorry

end TorchFire.TF
