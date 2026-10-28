-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_robustness_locc
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.robustness_locc
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:46:46.301376+00:00
-- url     : https://prove2.me/theorems/c8e3243d-e9d3-41ca-8414-5174eed5fce1
-- title:
--   Selective LOCC monotonicity of two robustness measures
-- statement:
--   Fix a finite adaptive LOCC protocol with arbitrary positive finite input and output dimensions, including a fixed final classical recording map. For input density matrix $\rho$, write $p_i$ and $\rho'_i$ for its probabilities and normalized positive-probability conditional outputs. Then both
--
--   $$\sum_{i:p_i>0}p_iN_{ss}(\rho'_i)\le N_{ss}(\rho),\qquad \sum_{i:p_i>0}p_iN_{ppts}(\rho'_i)\le N_{ppts}(\rho).$$
--
--   The two robustness measures are defined by their actual separable and PPT bases. This retains selective, rather than only deterministic, monotonicity.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §II.C, unnumbered claim, PDF p. 4. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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































/-- §II.C, PDF p. 4: both robustness quantities obey selective inequality (12). -/
theorem robustness_locc {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (P : Protocol a b c d) (o : ℕ) (record : ℕ → Fin o)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    letI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
    letI : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
    letI : Nonempty (Fin c) := ⟨⟨0,hc⟩⟩
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    selectiveAverage separableRobustness (recordedBranches (protocolBranches P rho) o record) ≤ separableRobustness rho ∧
    selectiveAverage pptRobustness (recordedBranches (protocolBranches P rho) o record) ≤ pptRobustness rho := by sorry

































end QAlgorithms.Papers.Independent.Independent1.P07
