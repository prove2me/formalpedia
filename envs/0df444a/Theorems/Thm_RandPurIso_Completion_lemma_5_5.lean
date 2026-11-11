-- Prove2me | Theorems.Thm_RandPurIso_Completion_lemma_5_5
-- name    : RandPurIso.Completion.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:31.864555+00:00
-- url     : https://prove2.me/theorems/e2a25921-44ca-456d-a6ba-4866e6d039f0
-- title:
--   Lemma 5.5 — $\widetilde{PR}$ keeps the recording register in $\Gamma$
-- statement:
--   In the setting of Theorem 5.4 ($1\le N<M$, $T<M$, $V$ an isometry, $D^V$ a completion), for $0\le t<T$,
--   $$\widetilde{PR}\,(I\otimes\Gamma_t)=(I\otimes\Gamma_{t+1})\,\widetilde{PR}\,(I\otimes\Gamma_t).$$
--   After $t<T$ applications of $\widetilde{PR}$ the internal state stays in $\Gamma$.
--
--   Differences from the source:
--   - encoding: ~Λ_t on H(M1)^{⊗t} → ~Λ_t extended by zero to input words with a letter outside M1; reason: ~PR is only applied to inputs in M1 with recordings in Γ_t
--   - encoding: f_λ = dim P_λ, d_{λ,N} = dim Q_{λ,N}, Π_{λ,t} → hook-length formula, Eq. (1), and QAlgorithms.Schur.isotypicProjector; reason: the paper's own formulas (p. 23); same values
--   - generalization: stated in §5.2 under the standing assumption T√(N/M) < c for a sufficiently small constant c (p. 34) → no smallness assumption; only 1 ≤ N < M, T < M, V an isometry, D^V a completion; reason: the proof on p. 34 uses only that the appended slots lie in Π_{M1} ⊗ conj(Π^{D^V}_{M1}) and permutation invariance, never the smallness of T√(N/M); adding the assumption gives the source's statement
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 5.5, p. 32 (restated p. 34)

import Mathlib
import Definitions.Def_RandPurIso_Completion_IsCompletion
import Definitions.Def_RandPurIso_Completion_relPathRecording
import Definitions.Def_RandPurIso_Completion_gammaT
open Matrix

namespace RandPurIso.Completion

/-- **Lemma 5.5** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 32, restated p. 34). For `0 ≤ t < T`,
`~PR (I ⊗ Γ_t) = (I ⊗ Γ_{t+1}) ~PR (I ⊗ Γ_t)`.

**Formalization Note.** The setting of the proof of Theorem 5.4: `1 ≤ N < M`, `T < M`, `V` an
isometry, `D^V` a completion of `V`; `~PR` is `relPathRecording` and `Γ_t` is `gammaT`. No smallness
assumption is used. -/
theorem lemma_5_5 (T M N : ℕ) (hN : 1 ≤ N) (hNM : N < M) (hTM : T < M)
    (V : Matrix (Fin M) (Fin N) ℂ) (hV : Vᴴ * V = 1) (D : Matrix.unitaryGroup (Fin M) ℂ)
    (hD : IsCompletion V D) (t : ℕ) (ht : t < T) :
    relPathRecording N T D * Matrix.kronecker (1 : Matrix (Fin M) (Fin M) ℂ) (gammaT N T D t) =
      Matrix.kronecker (1 : Matrix (Fin M) (Fin M) ℂ) (gammaT N T D (t + 1)) *
        relPathRecording N T D * Matrix.kronecker (1 : Matrix (Fin M) (Fin M) ℂ) (gammaT N T D t) := by sorry

end RandPurIso.Completion
