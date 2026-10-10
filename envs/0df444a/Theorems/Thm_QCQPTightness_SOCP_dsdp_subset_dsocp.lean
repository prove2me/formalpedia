-- Prove2me | Theorems.Thm_QCQPTightness_SOCP_dsdp_subset_dsocp
-- name    : QCQPTightness.SOCP.dsdp_subset_dsocp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:24:21.683761+00:00
-- url     : https://prove2.me/theorems/0dd8680e-f089-486f-9c74-d04b235ad482
-- title:
--   App. A, proof of Proposition 1, p. 34 — for a diagonal QCQP, 𝒟_SDP ⊆ 𝒟_SOCP
-- statement:
--   Let a QCQP (1) be in diagonal form (10), $A_i = \mathrm{Diag}(a_i)$ for $i \in [\![0, m]\!]$. Then the projected epigraph of the SDP relaxation (4) is contained in that of the SOCP relaxation (12):
--
--   $$
--   \mathcal{D}_{\mathrm{SDP}} \subseteq \mathcal{D}_{\mathrm{SOCP}}.
--   $$
--
--   This is the first half of the set identity in Proposition 1.
--
--   **Formalization Note** The standing assumption $m \ge 1$ is not needed and is dropped, which makes the statement stronger.
-- source:
--   arXiv:1911.09195v3, App. A, proof of Proposition 1, p. 34

import Mathlib
import Definitions.Def_QCQPTightness_SOCP_QCQP
import Definitions.Def_QCQPTightness_SOCP_Relaxation

namespace QCQPTightness.SOCP

open Matrix

/-- App. A, proof of Proposition 1, p. 34: for a diagonal QCQP (10), `𝒟_SDP ⊆ 𝒟_SOCP`. -/
theorem dsdp_subset_dsocp {N m : ℕ} (P : QCQP N m) (a₀ : Fin N → ℝ) (a : Fin m → Fin N → ℝ)
    (hdiag : P.IsDiagonalQCQP a₀ a) :
    P.DSDP ⊆ P.DSOCP a₀ a := by sorry

end QCQPTightness.SOCP
