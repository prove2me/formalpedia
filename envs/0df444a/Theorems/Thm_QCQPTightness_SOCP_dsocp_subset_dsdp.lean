-- Prove2me | Theorems.Thm_QCQPTightness_SOCP_dsocp_subset_dsdp
-- name    : QCQPTightness.SOCP.dsocp_subset_dsdp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:23:29.50319+00:00
-- url     : https://prove2.me/theorems/68036d3f-ba4f-4e86-8f55-71a98fc953fd
-- title:
--   App. A, proof of Proposition 1, pp. 34–35 — for a diagonal QCQP, 𝒟_SOCP ⊆ 𝒟_SDP
-- statement:
--   Let a QCQP (1) be in diagonal form (10), $A_i = \mathrm{Diag}(a_i)$ for $i \in [\![0, m]\!]$. Then the projected epigraph of the SOCP relaxation (12) is contained in that of the SDP relaxation (4):
--
--   $$
--   \mathcal{D}_{\mathrm{SOCP}} \subseteq \mathcal{D}_{\mathrm{SDP}}.
--   $$
--
--   This is the second half of the set identity in Proposition 1.
--
--   **Formalization Note** The standing assumption $m \ge 1$ is not needed and is dropped, which makes the statement stronger.
-- source:
--   arXiv:1911.09195v3, App. A, proof of Proposition 1, pp. 34–35

import Mathlib
import Definitions.Def_QCQPTightness_SOCP_QCQP
import Definitions.Def_QCQPTightness_SOCP_Relaxation

namespace QCQPTightness.SOCP

open Matrix

/-- App. A, proof of Proposition 1, pp. 34–35: for a diagonal QCQP (10), `𝒟_SOCP ⊆ 𝒟_SDP`. -/
theorem dsocp_subset_dsdp {N m : ℕ} (P : QCQP N m) (a₀ : Fin N → ℝ) (a : Fin m → Fin N → ℝ)
    (hdiag : P.IsDiagonalQCQP a₀ a) :
    P.DSOCP a₀ a ⊆ P.DSDP := by sorry

end QCQPTightness.SOCP
