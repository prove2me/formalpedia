-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_lemma_4_3
-- name    : QAdvFew.PoQOracle.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:54.202907+00:00
-- url     : https://prove2.me/theorems/ffdae262-db00-4f6b-91b6-63dc6645c8ff
-- title:
--   Lemma 4.3 — $\mathsf{BQP}^O=\mathsf{PSPACE}^O$ almost surely
-- statement:
--   With probability $1$ over $O=(A,B,C)\leftarrow\mathcal D$,
--   $$\mathsf{BQP}^O=\mathsf{PSPACE}^O.$$
--
--   The component $B$ encodes the answers of $\mathsf{PSPACE}$-type machines as Forrelated or uniform strings, which a quantum algorithm tells apart with property (1) of Lemma 3.10.
--
--   Differences from the source:
--   - generalization: the oracle distribution D built from the Forrelation distribution of [RT19] → D built from any family F with the properties of Lemma 3.10 used; reason: the construction of [RT19] is one such family by Lemma 3.10, and the paper's proof uses only these properties
--   - reading: machines of S_t syntactically restricted to query levels up to ⌊√t⌋ and to the time and space bounds → every pair of code length below t, run with the truncated oracle and clocks; reason: makes the recursion well-founded; same value on machines obeying the restrictions
--   - encoding: with probability 1 over O ← D → ∀ᵐ over the seed measure of the sampling map; reason: D is the law of the sampling map; no measurability of the event is needed
--   - encoding: classical oracles, Turing machines, the universal gate set → `Oracle = Str → Bool`, the finite-table machines `OTM`, Clifford+T with an XOR oracle gate; reason: an explicit model of the paper's §3.2 conventions; same classes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 4.3, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC
import Definitions.Def_QAdvFew_PoQOracle_BQP
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_QAdvFew_PoQOracle_ForrQuantum

open MeasureTheory

namespace QAdvFew.PoQOracle

/-- **Lemma 4.3** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*,
arXiv:2611.05303v1, Lemma 4.3, p. 22 (PDF p. 24)). With probability 1 over `O = (A, B, C) ← D`,
`BQP^O = PSPACE^O`.

**Formalization Note** `D` is built from any family `F` with property (1) of Lemma 3.10 (the only
property the proof uses); "with probability 1" is `∀ᵐ` over the seeds. -/
theorem lemma_4_3 (F : (N : ℕ) → PMF (Fin N → Bool)) (hF : ForrQuantum F) :
    ∀ᵐ ω ∂(seedMeasure F), BQP (sampleO ⊤ ω) = PSPACE (sampleO ⊤ ω) := by sorry

end QAdvFew.PoQOracle
