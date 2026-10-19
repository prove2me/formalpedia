-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_teleportation_singlet_distance
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.teleportation_singlet_distance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:47:54.497099+00:00
-- url     : https://prove2.me/theorems/6e005a40-8507-4472-ae25-ba7e05d25b0e
-- title:
--   Optimized teleportation and singlet distances
-- statement:
--   Let $m\ge1$ and let $\rho$ be an $m\times m$ bipartite density matrix. For a deterministic LOCC teleportation protocol $T$, let $\Lambda_{T,\rho}$ map Alice's unknown input state to Bob's output. Define $d_{\min}$ by taking the infimum over $T$ of the Haar average of $\||\phi\rangle\langle\phi|-\Lambda_{T,\rho}(|\phi\rangle\langle\phi|)\|_1$. Then
--
--   $$d_{\min}(\rho)=\frac m{m+1}\Delta(P_+,\rho).$$
--
--   The protocol is fixed before the unknown input. This optimized equality is the numbered result adapted from reference [27].
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §III.B, Lemma 5 (adapted from [27]), Eq. (37), PDF p. 6. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

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






















































/-- Lemma 5 (adapted from [27]), Eq. (37), PDF pp. 5–6. The optimized equality
uses infima; it does not assert invariance of an individual channel's distance under twirling. -/
theorem teleportation_singlet_distance {m : ℕ} (hm : 0 < m)
    (rho : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ) (hrho : IsDensityMatrix rho) :
    teleportationDistance hm rho = (m : ℝ)/(m+1)*singletDistance m hm rho := by sorry










end QAlgorithms.Papers.Independent.Independent1.P07
