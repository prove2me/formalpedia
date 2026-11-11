-- Prove2me | Theorems.Thm_RandPurIso_Completion_lemma_5_7
-- name    : RandPurIso.Completion.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:30.573468+00:00
-- url     : https://prove2.me/theorems/6829e96f-1a40-4809-a876-885d650574e9
-- title:
--   Lemma 5.7 — the right-hand terms vanish on $\Gamma$
-- statement:
--   In the setting of Theorem 5.4, for $0\le t<T$,
--   $$PR^\dagger_{[M],T}\,D^V(\Pi_{M_0}\otimes\Gamma_t)=\widetilde{PR}^\dagger D^V(\Pi_{M_0}\otimes\Gamma_t)=0,$$
--   with $D^V$ acting on $\mathcal H([M])$ and the identity on the recording register. Both equalities are stated.
--
--   Differences from the source:
--   - encoding: ~Λ_t on H(M1)^{⊗t} → extended by zero off H(M1)^{⊗t}; reason: ~PR is only applied to inputs in M1 with recordings in Γ_t
--   - generalization: stated in §5.2 under the standing assumption T√(N/M) < c for a sufficiently small constant c (p. 34) → no smallness assumption; only 1 ≤ N < M, T < M, V an isometry, D^V a completion; reason: the argument of p. 33 uses only that Γ_t keeps the output slots in conj(Im Π^{D^V}_{M1}) and Π^{D^V}_{M0}D^V = D^VΠ_{M0}, never the smallness of T√(N/M); adding the assumption gives the source's statement
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 5.7, p. 33 (proof pp. 39–40)

import Mathlib
import Definitions.Def_RandPurIso_Completion_IsCompletion
import Definitions.Def_RandPurIso_Completion_pathRecording
import Definitions.Def_RandPurIso_Completion_relPathRecording
import Definitions.Def_RandPurIso_Completion_gammaT
import Definitions.Def_RandPurIso_Completion_projM0
open Matrix

namespace RandPurIso.Completion

/-- **Lemma 5.7** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 33, proved pp. 39–40). For `0 ≤ t < T`,
`PR†_{[M],T} D^V (Π_{M0} ⊗ Γ_t) = ~PR† D^V (Π_{M0} ⊗ Γ_t) = 0`.

**Formalization Note.** `D^V` acts on `H([M])` with the identity on the recording register. The
setting is that of the proof of Theorem 5.4; no smallness assumption is used. -/
theorem lemma_5_7 (T M N : ℕ) (hN : 1 ≤ N) (hNM : N < M) (hTM : T < M)
    (V : Matrix (Fin M) (Fin N) ℂ) (hV : Vᴴ * V = 1) (D : Matrix.unitaryGroup (Fin M) ℂ)
    (hD : IsCompletion V D) (t : ℕ) (ht : t < T) :
    (pathRecording M T)ᴴ *
        Matrix.kronecker (D : Matrix (Fin M) (Fin M) ℂ) (1 : Matrix (PRSt M T) (PRSt M T) ℂ) *
        Matrix.kronecker (projM0 N M) (gammaT N T D t) = 0 ∧
      (relPathRecording N T D)ᴴ *
        Matrix.kronecker (D : Matrix (Fin M) (Fin M) ℂ) (1 : Matrix (PRSt M T) (PRSt M T) ℂ) *
        Matrix.kronecker (projM0 N M) (gammaT N T D t) = 0 := by sorry

end RandPurIso.Completion
