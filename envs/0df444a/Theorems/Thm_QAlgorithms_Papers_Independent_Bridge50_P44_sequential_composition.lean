-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_sequential_composition
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.sequential_composition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:21:05.755989+00:00
-- url     : https://prove2.me/theorems/8f297c76-9f95-4657-b985-fbc566e84721
-- title:
--   C.2.1: generic sequential composition
-- statement:
--   In an abstract three-interface AC resource model satisfying the converter wiring laws and the nonnegative contractive pseudometric axioms, let $R^\sharp,S^\diamond,T^\square$ be filtered resources. Suppose honest protocols $\pi$ and $\pi'$ construct $S^\diamond$ from $R^\sharp$ within $\varepsilon\ge0$, and $T^\square$ from that same $S^\diamond$ within $\varepsilon'\ge0$, in both clauses of Definition 2.1. Then
--
--   $$R^\sharp\xrightarrow{\pi'\pi,\,\varepsilon+\varepsilon'}T^\square.$$
--
--   The conclusion includes honest availability and existence of one simulator for the adversarial resource comparison. There is no restriction $\varepsilon+\varepsilon'\le1$. This is the generic AC composition result attributed to [MR11, Mau12], without specializing the abstract resources to an unimplemented QKD model.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 46, C.2.1: generic sequential composition

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

/-- PDF p.46, Appendix C.2.1: generic sequential AC composition. Both honest
availability and adversarial simulation are retained, with the same intermediate
resource and filter. Errors are nonnegative and need not sum to at most one. -/
theorem sequential_composition (M : ACModel) (p q : M.Converter × M.Converter)
    (r s t : Filtered M) (epsilon eta : ℝ) (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hp : Constructs M p r s epsilon) (hq : Constructs M q s t eta) :
    Constructs M (serialProtocol M q p) r t (epsilon + eta) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
