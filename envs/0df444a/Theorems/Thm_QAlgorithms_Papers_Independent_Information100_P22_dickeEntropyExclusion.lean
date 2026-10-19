-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_dickeEntropyExclusion
-- name    : QAlgorithms.Papers.Independent.Information100.P22.dickeEntropyExclusion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:16:25.307095+00:00
-- url     : https://prove2.me/theorems/01bab7f6-ec21-4871-a9c8-1b3f12c87491
-- title:
--   Eqs.(S71)–(S72), unnumbered: architecture-independent Dicke exclusions
-- statement:
--   Let $m\ge2$, $k\ge1$, $0\le r\le2mk$, and let $H(\lambda^{(r)})$ denote the exact balanced Dicke entropy above. Any AS unitary leaving $N$ untouched that permits all-output exact recovery must satisfy
--   $$(m-1)k\le H(\lambda^{(r)}).$$
--   Consequently either $H(\lambda^{(r)})<(m-1)k$ or $(m-1)k>\log_2(mk+1)$ excludes that Dicke resource for every such unitary. The inequalities are necessary, never sufficient. This is independent of the sector-wise Pauli obstruction.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 44, Eqs.(S71)–(S72), unnumbered: architecture-independent Dicke exclusions

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eqs.(S71)–(S72), PDF pp.14,44: only necessary entropy inequalities, with both exclusions. -/
theorem dickeEntropyExclusion (m k r : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) (hr : r ≤ 2*(m*k)) :
    (∀ U : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ,
      AllRecoverable (dickeResource (Wires m k) r) (U : Op _) →
        (((m-1)*k : ℕ) : ℝ) ≤ dickeEntropy (m*k) r) ∧
    ((((m-1)*k : ℕ) : ℝ) > Real.logb 2 (m*k+1) →
      ∀ U : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ,
        ¬ AllRecoverable (dickeResource (Wires m k) r) (U : Op _)) ∧
    (dickeEntropy (m*k) r < (((m-1)*k : ℕ) : ℝ) →
      ∀ U : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ,
        ¬ AllRecoverable (dickeResource (Wires m k) r) (U : Op _)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
