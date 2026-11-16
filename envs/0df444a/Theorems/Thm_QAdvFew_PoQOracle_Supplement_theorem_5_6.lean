-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_Supplement_theorem_5_6
-- name    : QAdvFew.PoQOracle.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:25:11.673362+00:00
-- url     : https://prove2.me/theorems/4b510680-68df-47cf-aa04-0dac3fb3d9d0
-- title:
--   Theorem 5.6 — $\mathsf{BQP}^{O,\mathsf{PSPACE}}=\mathsf{QCMA}^{O,\mathsf{PSPACE}}$ with probability $1$
-- statement:
--   With probability $1$ over $O\leftarrow\mathcal D$ (the oracle distribution of §5.1),
--
--   $$
--   \mathsf{BQP}^{O,\mathsf{PSPACE}}=\mathsf{QCMA}^{O,\mathsf{PSPACE}},
--   $$
--
--   where PSPACE is a fixed oracle for a PSPACE-complete problem and the classes are classes of languages.
--
--   This is the first half of Theorem 5.1: classical witnesses carry no useful information about the oracle, so every $\mathsf{QCMA}$ verifier can be replaced by one that does not need it.
--
--   Differences from the source:
--   - encoding: a fixed oracle PSPACE for a PSPACE-complete problem (§5.1) → every PSPACE-complete language Lps (∀ Lps, as the classical oracle x ↦ [x ∈ Lps]); reason: the paper fixes an arbitrary such oracle; stating it for every choice is the same claim
--   - encoding: with probability 1 over O ← D (the oracle distribution of §5.1) → ∀ᵐ ω ∂Dmeasure, with O = oracleD ω; Haar states |ϕ_x⟩ sampled as V_x|0⟩; the purifications of σ_t and ρ_x fixed explicitly; reason: the oracle is a function of the independent samples; Haar-random W's make the law independent of the choice of purification
--   - encoding: QPT/nonuniform QPT algorithms and parties with oracle access, as in §3.2.1–§3.2.2 → uniform (resp. arbitrary) polynomially bounded families of Clifford+T circuits with classical-oracle gates and controlled/inverse unitary-oracle gates; size = binary description length plus t per level-t query; component/level superposition via controlled queries; reason: Lean representation of the paper's conventions; polynomially equivalent
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 5.6, p. 40 (PDF p. 42)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_oracleD
import Definitions.Def_QAdvFew_PoQOracle_Supplement_BQPU
import Definitions.Def_QAdvFew_PoQOracle_Supplement_QCMAU
import Definitions.Def_QAdvFew_PoQOracle_Supplement_IsPSPACEComplete

open QAlgorithms.Complexity MeasureTheory

namespace QAdvFew.PoQOracle.Supplement

/-- **Theorem 5.6** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 5.6, p. 40 (PDF p. 42)): "With probability 1 over `O ← D`,
`BQP^{O,PSPACE} = QCMA^{O,PSPACE}`."

For every PSPACE-complete language `Lps` (the fixed oracle PSPACE of §5.1, p. 33), for
`Dmeasure`-almost every sample `ω` the classes of languages `BQP^{O,Lps}` and `QCMA^{O,Lps}` with
`O = oracleD ω` (the oracle `(SG, Expand, Mix)` of §5.1) are equal.

**Formalization Note** The probability-1 quantifier is outside the class equality, so the exceptional
set does not depend on the language (the proof's countable union over verifiers, p. 41). -/
theorem theorem_5_6 (Lps : Set Str) (hL : IsPSPACEComplete Lps) :
    ∀ᵐ ω ∂Dmeasure, BQPU (oracleD ω) (langOracle Lps) = QCMAU (oracleD ω) (langOracle Lps) := by sorry

end QAdvFew.PoQOracle.Supplement
