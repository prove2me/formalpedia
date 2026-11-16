-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_Supplement_theorem_5_1
-- name    : QAdvFew.PoQOracle.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:23:35.054451+00:00
-- url     : https://prove2.me/theorems/07df5eb0-ef18-450d-864b-1352db390b72
-- title:
--   Theorem 5.1 — $\mathsf{BQP}^{O,\mathsf{PSPACE}}=\mathsf{QCMA}^{O,\mathsf{PSPACE}}$ and qv-OSP almost surely
-- statement:
--   Let $\mathcal D$ be the distribution over unitary oracles $O=(\mathrm{SG},\mathrm{Expand},\mathrm{Mix})$ of §5.1 and let PSPACE be a fixed oracle for a PSPACE-complete problem. With probability $1$ over $O\leftarrow\mathcal D$:
--
--   1. $O$ is unitary and $\mathsf{BQP}^{O,\mathsf{PSPACE}}=\mathsf{QCMA}^{O,\mathsf{PSPACE}}$;
--   2. relative to $(O,\mathsf{PSPACE})$, quantum-verifier oblivious state preparation exists.
--
--   This is the paper's second main result; Theorem 1.8 follows from it.
--
--   Differences from the source:
--   - reading: there exists a distribution over unitary oracles O ← D → the distribution D constructed in §5.1 (Dmeasure, oracleD), with unitarity of O asserted almost surely; reason: the paper's theorem names the D of §5.1 and proves it for that D; the explicit statement implies the printed existential
--   - encoding: a fixed oracle PSPACE for a PSPACE-complete problem (§5.1) → every PSPACE-complete language Lps (∀ Lps, as the classical oracle x ↦ [x ∈ Lps]); reason: the paper fixes an arbitrary such oracle; stating it for every choice is the same claim
--   - encoding: with probability 1 over O ← D (the oracle distribution of §5.1) → ∀ᵐ ω ∂Dmeasure, with O = oracleD ω; Haar states |ϕ_x⟩ sampled as V_x|0⟩; the purifications of σ_t and ρ_x fixed explicitly; reason: the oracle is a function of the independent samples; Haar-random W's make the law independent of the choice of purification
--   - encoding: QPT/nonuniform QPT algorithms and parties with oracle access, as in §3.2.1–§3.2.2 → uniform (resp. arbitrary) polynomially bounded families of Clifford+T circuits with classical-oracle gates and controlled/inverse unitary-oracle gates; size = binary description length plus t per level-t query; component/level superposition via controlled queries; reason: Lean representation of the paper's conventions; polynomially equivalent
--   - encoding: probabilities over the parties' randomness and measurements in a protocol with classical communication → sum over transcripts of the product of the two parties' likelihoods; messages of one fixed polynomial length (zero-padded); reason: the standard decomposition for classical communication; a polynomial-time party reads polynomially many bits
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 5.1, p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_oracleD
import Definitions.Def_QAdvFew_PoQOracle_Supplement_BQPU
import Definitions.Def_QAdvFew_PoQOracle_Supplement_QCMAU
import Definitions.Def_QAdvFew_PoQOracle_Supplement_IsPSPACEComplete
import Definitions.Def_QAdvFew_PoQOracle_Supplement_IsQvOSP

open QAlgorithms.Complexity MeasureTheory

namespace QAdvFew.PoQOracle.Supplement

/-- **Theorem 5.1** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 5.1, p. 32 (PDF p. 34)): "There exists a distribution over unitary
oracles `O ← D` such that with probability 1, 1. `BQP^{O,PSPACE} = QCMA^{O,PSPACE}` 2. Relative to
`O, PSPACE`, quantum verifier oblivious state preparation exists."

Stated for the distribution `D` that §5.1 constructs (`Dmeasure`, `oracleD`): for every
PSPACE-complete language `Lps`, for almost every sample `ω`, the oracle `O = oracleD ω` is unitary,
`BQP^{O,Lps} = QCMA^{O,Lps}`, and qv-OSP (Definition 3.28) exists relative to `(O, Lps)`.

**Formalization Note** The explicit `D` witnesses the printed existential over distributions; the
paper proves the theorem for this `D` (§5.3–§5.4, PDF pp. 42–47). -/
theorem theorem_5_1 (Lps : Set Str) (hL : IsPSPACEComplete Lps) :
    ∀ᵐ ω ∂Dmeasure, (oracleD ω).IsUnitary ∧
      BQPU (oracleD ω) (langOracle Lps) = QCMAU (oracleD ω) (langOracle Lps) ∧
      QvOSPExists (oracleD ω) (langOracle Lps) := by sorry

end QAdvFew.PoQOracle.Supplement
