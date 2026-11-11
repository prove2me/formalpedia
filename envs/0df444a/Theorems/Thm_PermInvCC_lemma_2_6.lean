-- Prove2me | Theorems.Thm_PermInvCC_lemma_2_6
-- name    : PermInvCC.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:54.528815+00:00
-- url     : https://prove2.me/theorems/96fbde85-1359-450b-b854-46f1f4a77672
-- title:
--   Lemma 2.6 — count formula $H(J_W,J_V)^2=\sum_e(\sqrt{W_e}-\sqrt{V_e})^2/(w+v)$
-- statement:
--   For nonnegative weight vectors $W,V$ with totals $w,v$,
--   $$H(J_W,J_V)^2=\frac{\sum_e\bigl(\sqrt{W_e}-\sqrt{V_e}\bigr)^2}{w+v}, \tag{2.4}$$
--   with the same zero-denominator convention (value $0$). In particular, for tables $T,U$ with the same margins and every event $E\in\mathcal E$,
--   $$H(J^E_T,J^E_U)=h_E(T,U).$$
--
--   The lemma identifies the cut separations with Hellinger distances, so that sampling estimates of the counts control the separations.
--
--   **Formalization Note** $H$ is defined by the integrals of Definition 2.5, not by this formula.
--
--   Differences from the source:
--   - generalization: nonnegative count vectors W, V indexed by the cells of an event → nonnegative real weights on any finite label set; reason: integer counts on the cells of E are a special case; the paper applies (2.4) to the real weights Z_e/p in App. C.3
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 2.6, eq. (2.4), p.10

import Mathlib
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_cutEvents
import Definitions.Def_PermInvCC_hE
import Definitions.Def_PermInvCC_hell
import Definitions.Def_PermInvCC_J

namespace PermInvCC

/-- **Lemma 2.6 (Count Formula for Hellinger Distance)** (Y. Huang and Z. Ye, arXiv:2609.40116,
held version sha256 fe1797dd…, p.10). For nonnegative count vectors `W, V` of totals `w, v`,
`H(J_W, J_V)² = ∑_e (√W_e − √V_e)² / (w + v)`, with the zero-denominator convention (value `0`).
In particular `H(J^E_T, J^E_U) = h_E(T, U)`.

**Formalization Note.** The first clause is stated for nonnegative real weights on any finite
label set (the paper applies it to the real weights `Z_e/p` in App. C.3); Lean's real division by
zero gives the convention `0`. The second clause is for tables with the same margins and an
event `E ∈ 𝓔`, where `h_E` is defined (Definition 2.4). `H` is defined from the integrals of
Definition 2.5, not from this formula. -/
theorem lemma_2_6 :
    (∀ (ι : Type) [Fintype ι] (W V : ι → ℝ) (hW : ∀ e, 0 ≤ W e) (hV : ∀ e, 0 ≤ V e),
      hell (J W hW) (J V hV) ^ 2 =
        (∑ e, (Real.sqrt (W e) - Real.sqrt (V e)) ^ 2) / (∑ e, W e + ∑ e, V e)) ∧
    (∀ (q : ℕ), 2 ≤ q → ∀ E ∈ cutEvents q, ∀ T U : Fin q → Fin q → ℕ,
      (∀ a, rowMargin T a = rowMargin U a) → (∀ b, colMargin T b = colMargin U b) →
      hell (JE E T) (JE E U) = hE E T U) := by sorry

end PermInvCC
