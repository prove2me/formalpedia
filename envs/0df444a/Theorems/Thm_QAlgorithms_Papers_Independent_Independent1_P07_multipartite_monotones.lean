-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_multipartite_monotones
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.multipartite_monotones
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:48:21.68189+00:00
-- url     : https://prove2.me/theorems/ee79047f-d3c1-4824-bf27-c509239c074d
-- title:
--   Three grouped tripartite negativity monotones
-- statement:
--   For a tripartite density matrix, let $M_0=N_{AB|C}$, $M_1=N_{AC|B}$, and $M_2=N_{BC|A}$. For every finite adaptive LOCC protocol acting on the three separated parties, with normalized positive-probability outputs $\rho'_i$ and probabilities $p_i$, all three grouped negativities obey
--
--   $$\forall k\in\{0,1,2\},\qquad \sum_{i:p_i>0}p_iM_k(\rho'_i)\le M_k(\rho).$$
--
--   All regroupings are computed from the same state. Local dimensions may change, and a fixed final coarse-graining is allowed. The other three functions in threePartyMeasures are reduced-state negativities defined by the source for a noncooperating discarded party; this theorem makes no monotonicity assertion about them under three-party LOCC.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §VI.A and note [33], PDF pp. 10–11, PDF p. 10. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement
































































/-- Section VI.A and note [33], PDF pp. 10-11: the three grouped splittings are
selective entanglement monotones for separated-party LOCC. The reduced-state
quantities describe a noncooperating discarded party; they are not asserted
monotone when that party participates in the protocol. -/
theorem multipartite_monotones {a b c x y z : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (P : ThreePartyProtocol a b c x y z) (o : ℕ) (record : ℕ → Fin o)
    (rho : Matrix (Fin a × (Fin b × Fin c)) (Fin a × (Fin b × Fin c)) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∀ k : Fin 3,
      ((recordedBranches (threePartyBranches P rho) o record).map fun X => if 0 < X.trace.re then
        X.trace.re*threePartyMeasures ((X.trace.re : ℂ)⁻¹ • X) (Fin.castAdd 3 k) else 0).sum ≤
          threePartyMeasures rho (Fin.castAdd 3 k) := by sorry
end QAlgorithms.Papers.Independent.Independent1.P07
