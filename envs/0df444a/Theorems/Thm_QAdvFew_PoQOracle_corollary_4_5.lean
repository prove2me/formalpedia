-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_corollary_4_5
-- name    : QAdvFew.PoQOracle.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:42.806828+00:00
-- url     : https://prove2.me/theorems/80240553-9b08-406d-be35-4afbc9dae634
-- title:
--   Corollary 4.5 — $\mathsf{IP}^A=\mathsf{PSPACE}^A$
-- statement:
--   For every oracle $O=(A,B,C)$ in the support of $\mathcal D$,
--   $$\mathsf{IP}^A=\mathsf{PSPACE}^A.$$
--
--   Here $A$ is queried on its own. The paper stresses (Remark 4.6) that the equality is not claimed for the whole oracle $O$.
--
--   Differences from the source:
--   - reading: any oracle in the support of D → every outcome of the sampling map on every seed; reason: at least as strong as the topological support
--   - encoding: classical oracles, Turing machines, the universal gate set → `Oracle = Str → Bool`, the finite-table machines `OTM`, Clifford+T with an XOR oracle gate; reason: an explicit model of the paper's §3.2 conventions; same classes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Corollary 4.5, p. 23 (PDF p. 25)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_QAdvFew_PoQOracle_IP

namespace QAdvFew.PoQOracle

/-- **Corollary 4.5** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Corollary 4.5, p. 23 (PDF p. 25)). Let `O = (A, B, C)` be any
oracle in the support of `D`; then `IP^A = PSPACE^A`.

**Formalization Note** `A = (sampleABC ⊤ ω).1 = affineOracle RO`, queried on its own (not through
the join); the support is every outcome of the sampling map. -/
theorem corollary_4_5 (ω : Seed) : IP (sampleABC ⊤ ω).1 = PSPACE (sampleABC ⊤ ω).1 := by sorry

end QAdvFew.PoQOracle
