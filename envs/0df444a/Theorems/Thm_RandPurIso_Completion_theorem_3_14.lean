-- Prove2me | Theorems.Thm_RandPurIso_Completion_theorem_3_14
-- name    : RandPurIso.Completion.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:46.920734+00:00
-- url     : https://prove2.me/theorems/98db5e4d-b67d-4d33-b3fc-6458b24199e1
-- title:
--   Theorem 3.14 — exact path recording simulates controlled Haar queries
-- statement:
--   For every oracle algorithm $A$ making $t\le T$ controlled forward queries,
--   $$\mathop{\mathbb E}_{U\leftarrow\mathrm{Haar}([N])}\big[A^{\mathrm{ctrl}[U]}\big]=A^{\mathrm{ctrl}[PR_{[N],T}]},$$
--   where $\mathrm{ctrl}[U]=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes U$, $\mathrm{ctrl}[PR]=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes PR_{[N],T}$ and the recording register starts in $|\varnothing\rangle$. This is Theorem 5.3 and §2.1.1 of [FLM+26]; the paper uses it in dimension $M-N$ for the hybrid $W_1\to W_2$.
--
--   Differences from the source:
--   - reading: A^{ctrl[PR]} with the stateful partial isometry ctrl[PR] → contractionOracle: failure embedded as |⊥⟩ ⊗ |∅⟩; reason: Definition 3.2 needs the output in the form Out' ⊗ St
--   - encoding: E over U ← Haar([N]) → Bochner integral against the Haar probability measure on U(N) (QAlgorithms.Schur.unitaryHaar); reason: the integrand is continuous on a compact group
--   - generalization: A^O := A^O(|0⟩⟨0|_{Out,A}) on the workspace A (Definition 3.2) → any finite workspace W and any initial density matrix of the algorithm (OracleAlg.init); reason: Definition 3.2's "without loss of generality"; |0⟩⟨0| is the special case init = |0⟩⟨0|
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 3.14, p. 24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_contractionOracle
import Definitions.Def_RandPurIso_Completion_ctrlMap
import Definitions.Def_RandPurIso_Completion_pathRecording
open Matrix
open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace RandPurIso.Completion

/-- **Theorem 3.14 (exact simulation, Theorem 5.3 and Section 2.1.1 of [FLM+26])** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 24).

For every oracle algorithm `A` making `t ≤ T` controlled forward queries,
`E_{U←Haar([N])} [A^{ctrl[U]}] = A^{ctrl[PR_{[N],T}]}`.

**Formalization Note.** `ctrl[U] = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` and `ctrl[PR] = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ PR`
(identity on the recording register in the idle branch), both used through `Φ` (Definition 3.4);
the recording register starts in `|∅⟩`. `E_U` is the Bochner integral against the Haar probability
measure on `U(N)`. -/
theorem theorem_3_14 (N T : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (A : OracleAlg (Bool × Fin N) (Option (Bool × Fin N)) W) (hA : A.numQueries ≤ T) :
    ∫ U, A.run (contractionOracle (liftUnit (ctrlMap true (U : Matrix (Fin N) (Fin N) ℂ) 1)) unitInit)
        ∂(QAlgorithms.Schur.unitaryHaar N) =
      A.run (contractionOracle (ctrlSt (ctrlMap true (pathRecording N T) 1)) (emptyRecInit N T)) := by sorry

end RandPurIso.Completion
