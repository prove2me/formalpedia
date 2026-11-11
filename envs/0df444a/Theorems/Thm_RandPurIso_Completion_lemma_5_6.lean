-- Prove2me | Theorems.Thm_RandPurIso_Completion_lemma_5_6
-- name    : RandPurIso.Completion.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:23.947916+00:00
-- url     : https://prove2.me/theorems/bc38d5a5-9a35-4ac5-9937-8279a0c391a3
-- title:
--   Lemma 5.6 — $\widetilde{PR}$ and $PR_{[M],T}$ are close on $\Gamma$
-- statement:
--   Under the standing assumption of §5.2 ($T\sqrt{N/M}<c$), in the setting of Theorem 5.4, for $0\le t<T$,
--   $$\Big\|\big(\widetilde{PR}-PR_{[M],T}\big)(\Pi_{M_1}\otimes\Gamma_t)\Big\|_{op}\le3\sqrt{\frac{2N}{M-t}},$$
--   and in particular
--   $$\Big\|\big(\widetilde{PR}-PR_{[M],T}\big)(\Pi_{M_1}\otimes\Gamma)\Big\|_{op}\le3\sqrt{\frac{2N}{M-T+1}},\qquad\Gamma=\bigoplus_{t=0}^{T-1}\Gamma_t .$$
--
--   Differences from the source:
--   - encoding: a sufficiently small constant c → ∃ c > 0 before all parameters (its own c for this item); reason: the paper never fixes c
--   - encoding: ~Λ_t on H(M1)^{⊗t} → extended by zero off H(M1)^{⊗t}; reason: the operator is only evaluated on Π_{M1} ⊗ Γ_t
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Lemma 5.6, p. 33 (restated p. 34)

import Mathlib
import Definitions.Def_RandPurIso_Completion_IsCompletion
import Definitions.Def_RandPurIso_Completion_pathRecording
import Definitions.Def_RandPurIso_Completion_relPathRecording
import Definitions.Def_RandPurIso_Completion_gammaT
import Definitions.Def_RandPurIso_Completion_projM0
import Definitions.Def_RandPurIso_Completion_opNorm
open Matrix

namespace RandPurIso.Completion

/-- **Lemma 5.6** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 33, restated p. 34). For `0 ≤ t < T`,
`‖(~PR − PR_{[M],T})(Π_{M1} ⊗ Γ_t)‖_op ≤ 3 √(2N/(M − t))`. In particular,
`‖(~PR − PR_{[M],T})(Π_{M1} ⊗ Γ)‖_op ≤ 3 √(2N/(M − T + 1))`, `Γ = ⊕_{t=0}^{T−1} Γ_t`.

**Formalization Note.** Both clauses are stated. The standing assumption of §5.2 (p. 34), "`T√(N/M) < c` for some sufficiently small constant
`c`", is stated as `∃ c > 0` before all parameters; the setting is that of the proof of Theorem 5.4
(`1 ≤ N < M`, `T < M`, `V` an isometry, `D^V` a completion). `PR_{{[M],T}}` is `pathRecording M T`,
`~PR` is `relPathRecording`, `Γ_t` is `gammaT`, `Π^{{D^V}}_{{Mb}}` is `rotProj D (projMb)`, and the
operator norm is `opNorm` (Definition 3.1). `Γ` is `gammaAll`. -/
theorem lemma_5_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ (T M N : ℕ), 1 ≤ N → N < M → T < M →
      ∀ (V : Matrix (Fin M) (Fin N) ℂ), Vᴴ * V = 1 →
      ∀ (D : Matrix.unitaryGroup (Fin M) ℂ), IsCompletion V D →
      (T : ℝ) * Real.sqrt ((N : ℝ) / M) < c →
      (∀ t : ℕ, t < T →
        opNorm ((relPathRecording N T D - pathRecording M T) *
            Matrix.kronecker (projM1 N M) (gammaT N T D t))
          ≤ 3 * Real.sqrt (2 * (N : ℝ) / ((M : ℝ) - t))) ∧
      opNorm ((relPathRecording N T D - pathRecording M T) *
          Matrix.kronecker (projM1 N M) (gammaAll N T D))
        ≤ 3 * Real.sqrt (2 * (N : ℝ) / ((M : ℝ) - T + 1)) := by sorry

end RandPurIso.Completion
