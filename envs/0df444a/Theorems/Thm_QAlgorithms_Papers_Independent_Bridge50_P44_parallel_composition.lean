-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_parallel_composition
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.parallel_composition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:21:55.504351+00:00
-- url     : https://prove2.me/theorems/7016da2c-e075-426b-8c87-8a883da29a3c
-- title:
--   C.2.2: generic parallel composition
-- statement:
--   In an abstract three-interface AC model with the source's converter wiring and contractive pseudometric axioms, suppose honest protocols $\pi,\pi'$ construct $S^\diamond,S'^\square$ from $R^\sharp,R'^\flat$ within nonnegative errors $\varepsilon,\varepsilon'$, respectively, in both clauses of Definition 2.1. Then
--
--   $$R^\sharp\parallel R'^\flat\xrightarrow{\pi\parallel\pi',\,\varepsilon+\varepsilon'}S^\diamond\parallel S'^\square.$$
--
--   The parallel filtered resource contains both honest filters, and the conclusion retains both availability and existence of a simulator. Resource distance permits joint attacks and distinguishers; independence is not imposed. This is the generic abstract parallel construction theorem.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 47, C.2.2: generic parallel composition

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.47, Appendix C.2.2: generic parallel AC composition. The resource
metric permits joint distinguishers; independence of attacks is not assumed. -/
theorem parallel_composition (M : ACModel) (p q : M.Converter × M.Converter)
    (r s rprime sprime : Filtered M) (epsilon eta : ℝ)
    (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hp : Constructs M p r s epsilon) (hq : Constructs M q rprime sprime eta) :
    Constructs M (parallelProtocol M p q) (parallelFiltered M r rprime)
      (parallelFiltered M s sprime) (epsilon + eta) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
