-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_dickeSingleOutput
-- name    : QAlgorithms.Papers.Independent.Information100.P22.dickeSingleOutput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:16:58.480714+00:00
-- url     : https://prove2.me/theorems/e1d29ea1-5bb0-467b-9434-c1c1646c7048
-- title:
--   §V D / S4.4, unnumbered: Dicke failure at the single-output boundary
-- statement:
--   Let $m=1$, $k\ge1$, and $0\le r\le2k$. No Dicke resource admits an AS unitary that both conceals $S$ and exactly recovers the complete input from $SN$. For $k>1$,
--   $$\operatorname{rank}\rho_S\le k+1<2^k,\qquad\rho_S\ne I/2^k.$$
--   The $k=1$ obstruction instead comes from AME$(4,2)$ nonexistence. This excludes the Dicke family and does not assert unrestricted single-output impossibility at larger input dimensions.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 44, §V D / S4.4, unnumbered: Dicke failure at the single-output boundary

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- PDF pp.15,44: Dicke failure at m=1; k=1 uses the separate AME obstruction. -/
theorem dickeSingleOutput (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 2*k) :
    (∀ U : Matrix.unitaryGroup (Qubits k × Signals 1 k) ℂ,
      ¬ (Concealed (dickeResource (Wires 1 k) r) (U : Op _) 0 ∧
        AllRecoverable (dickeResource (Wires 1 k) r) (U : Op _))) ∧
    (1 < k → (rhoS (dickeResource (Wires 1 k) r)).rank ≤ k+1 ∧ k+1 < 2^k ∧
      rhoS (dickeResource (Wires 1 k) r) ≠ mixed (Signals 1 k)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
