-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_logarithmic_negativity_deterministic
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.logarithmic_negativity_deterministic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:47:45.122002+00:00
-- url     : https://prove2.me/theorems/0704ef7c-ee34-45ce-b43f-226da068aa41
-- title:
--   Deterministic logarithmic-negativity monotonicity
-- statement:
--   For any finite deterministic LOCC protocol $P$ and any bipartite density matrix $\rho$,
--
--   $$E_N(P(\rho))\le E_N(\rho).$$
--
--   Here $P(\rho)$ sums all subnormalized leaves after forgetting the transcript; input and output local dimensions may differ. This is the deterministic monotonicity asserted in the introduction and supported by §II.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §I–II, sentence crossing PDF pp. 1–2, PDF p. 1. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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
































/-- Introduction, PDF pp. 1–2: deterministic logarithmic-negativity monotonicity. -/
theorem logarithmic_negativity_deterministic {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (P : Protocol a b c d) (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hrho : IsDensityMatrix rho) : logNeg (protocolOutput P rho) ≤ logNeg rho := by sorry
































end QAlgorithms.Papers.Independent.Independent1.P07
