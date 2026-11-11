-- Prove2me | Theorems.Thm_RandPurIso_Completion_claim_1
-- name    : RandPurIso.Completion.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:14.640207+00:00
-- url     : https://prove2.me/theorems/9cb80b93-b2c9-407e-9ad2-fad68ce3b931
-- title:
--   Claim 1 — the $\Pi^{D^V}_{M_1}$ part: $\le 3(t+1)N/(M-t)$
-- statement:
--   Under the standing assumption of §5.2 that $T\sqrt{N/M}<c$ for a sufficiently small absolute constant $c>0$, in the setting of Theorem 5.4, for $0\le t<T$,
--   $$\Big\|\Pi^{D^V}_{M_1}\big(PR_{[M],T}-\widetilde{PR}\big)(\Pi_{M_1}\otimes\Gamma_t)\Big\|_{op}\le\frac{3(t+1)N}{M-t}.$$
--
--   Differences from the source:
--   - encoding: a sufficiently small constant c → ∃ c > 0 before all parameters (its own c for this item); reason: the paper never fixes c
--   - encoding: ~Λ_t on H(M1)^{⊗t} → extended by zero off H(M1)^{⊗t}; reason: the operator is only evaluated on Π_{M1} ⊗ Γ_t
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Claim 1, p. 35

import Mathlib
import Definitions.Def_RandPurIso_Completion_IsCompletion
import Definitions.Def_RandPurIso_Completion_pathRecording
import Definitions.Def_RandPurIso_Completion_relPathRecording
import Definitions.Def_RandPurIso_Completion_gammaT
import Definitions.Def_RandPurIso_Completion_projM0
import Definitions.Def_RandPurIso_Completion_opNorm
open Matrix

namespace RandPurIso.Completion

/-- **Claim 1** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 35, in the proof of Lemma 5.6). For `0 ≤ t < T`,
`‖Π^{D^V}_{M1} (PR_{[M],T} − ~PR)(Π_{M1} ⊗ Γ_t)‖_op ≤ 3(t + 1)N/(M − t)`.

**Formalization Note.** The standing assumption of §5.2 (p. 34), "`T√(N/M) < c` for some sufficiently small constant
`c`", is stated as `∃ c > 0` before all parameters; the setting is that of the proof of Theorem 5.4
(`1 ≤ N < M`, `T < M`, `V` an isometry, `D^V` a completion). `PR_{{[M],T}}` is `pathRecording M T`,
`~PR` is `relPathRecording`, `Γ_t` is `gammaT`, `Π^{{D^V}}_{{Mb}}` is `rotProj D (projMb)`, and the
operator norm is `opNorm` (Definition 3.1). -/
theorem claim_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (T M N : ℕ), 1 ≤ N → N < M → T < M →
      ∀ (V : Matrix (Fin M) (Fin N) ℂ), Vᴴ * V = 1 →
      ∀ (D : Matrix.unitaryGroup (Fin M) ℂ), IsCompletion V D →
      (T : ℝ) * Real.sqrt ((N : ℝ) / M) < c →
      ∀ t : ℕ, t < T →
        opNorm (Matrix.kronecker (rotProj D (projM1 N M)) (1 : Matrix (PRSt M T) (PRSt M T) ℂ) *
            (pathRecording M T - relPathRecording N T D) *
            Matrix.kronecker (projM1 N M) (gammaT N T D t))
          ≤ 3 * ((t : ℝ) + 1) * N / ((M : ℝ) - t) := by sorry

end RandPurIso.Completion
