-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_21
-- name    : SpencerEight.lemma_8_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:05.954771+00:00
-- url     : https://prove2.me/theorems/b336aee5-91e8-42f7-beb8-3b31d73f86f1
-- title:
--   Lemma 8.21 — uniform bound for the infinite tail
-- statement:
--   For every family of $m\le N$ symmetric contractions in $\mathbb R^{N\times N}$ with $u:=\log(N/m)>731/256$,
--   $$\Pr\Bigl[\bigl\|\sum_{i=1}^m\xi_iA_i\bigr\|\le185u\sqrt m\Bigr]\ge e^{-0.000051714m}.$$
--   Consequently, let $s$ be a coding amplitude satisfying Eq. (59) and let $0<v<e^{-731/256}$. Every residual family of at most $vn$ symmetric contractions in $\mathbb R^{n\times n}$ has a complete signing of norm at most $\mathcal T_s(v)\sqrt n$, where $\mathcal T_s$ is given by Eq. (90).
--
--   The bound closes every finite schedule of partial signings.
--
--   Differences from the source:
--   - encoding: u := log(N/m) > 731/256 → Real.log (N/m) with the same strict inequality, which is false at m = 0 because log 0 = 0 in Lean; reason: so m ≥ 1, as the source intends
--   - encoding: a family of at most vn matrices → a family indexed by Fin m with m ≤ vn, m = 0 allowed; reason: the same families
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.21, p.84 (PDF p.84)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_signedSum
import Definitions.Def_SpencerEight_CodingAmplitude
import Definitions.Def_SpencerEight_tailCost
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Lemma 8.21 (Uniform bound for the infinite tail), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.84 (PDF p.84). The measure bound and the complete signing with cost `T_s(v)` of Eq. (90).

**Formalization Note** `u = log(N/m) > 731/256` forces `1 ≤ m < N`: at `m = 0` Lean's value is `log 0 = 0`. `s` is any coding amplitude, not `s₊`. The residual family may be empty. -/
theorem lemma_8_21 :
    (∀ (m N : ℕ) (A : Fin m → Matrix (Fin N) (Fin N) ℝ), m ≤ N → (∀ i, IsSymmContraction (A i)) →
      731 / 256 < Real.log ((N : ℝ) / m) →
      ENNReal.ofReal (Real.exp (-(0.000051714 * (m : ℝ)))) ≤
        gammaM (Fin m) {ξ | ‖signedSum A ξ‖ ≤ 185 * Real.log ((N : ℝ) / m) * Real.sqrt m}) ∧
    (∀ s v : ℝ, CodingAmplitude s → 0 < v → v < Real.exp (-(731 / 256)) →
      ∀ (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ), (m : ℝ) ≤ v * n →
        (∀ i, IsSymmContraction (A i)) →
        ∃ ε : Fin m → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ‖signedSum A ε‖ ≤ tailCost s v * Real.sqrt n) := by sorry

end SpencerEight
