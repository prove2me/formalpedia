-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_negativity_locc
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.negativity_locc
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:46:47.604653+00:00
-- url     : https://prove2.me/theorems/c7960be2-bdde-48cc-bd1d-c9bb28865872
-- title:
--   Selective LOCC monotonicity of negativity
-- statement:
--   Fix a finite adaptive LOCC protocol before a bipartite density matrix $\rho$ is supplied. Local instruments may change finite dimensions, add ancillas, discard systems, and choose later operations from prior outcomes. After any fixed classical coarse-graining, let $X_i$ be its subnormalized outputs, $p_i=\operatorname{Tr}X_i$, and $\rho'_i=X_i/p_i$ for $p_i>0$. Then
--
--   $$\sum_{i:p_i>0}p_iN(\rho'_i)\le N(\rho).$$
--
--   Zero-probability outcomes contribute zero. This is the selective entanglement-monotone inequality.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §II.B, Proposition 3, Eq. (17), PDF p. 4. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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






























/-- Proposition 3, Eq. (17), PDF pp. 3–4: average monotonicity for adaptive LOCC. -/
theorem negativity_locc {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (P : Protocol a b c d) (o : ℕ) (record : ℕ → Fin o)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    selectiveAverage negativity (recordedBranches (protocolBranches P rho) o record) ≤ negativity rho := by sorry


































end QAlgorithms.Papers.Independent.Independent1.P07
