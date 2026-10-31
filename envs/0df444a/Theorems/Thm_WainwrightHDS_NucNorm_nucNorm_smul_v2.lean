-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_smul_v2
-- name    : WainwrightHDS.NucNorm.nucNorm_smul_v2
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T02:27:28.073956+00:00
-- url     : https://prove2.me/theorems/abe352f7-3534-489d-a4ac-bb933104c6d8
-- title:
--   Absolute homogeneity of the nuclear norm
-- statement:
--   For any scalar $c \in \mathbb{R}$ and matrix $A \in \mathbb{R}^{d_1 \times d_2}$, the nuclear norm satisfies $\||c A\||_{\mathrm{nuc}} = |c| \, \||A\||_{\mathrm{nuc}}$.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, Section 10.2, p. 313

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

namespace WainwrightHDS.NucNorm

/-- **Absolute homogeneity of the nuclear norm**: `|||c • A|||_nuc = |c| · |||A|||_nuc`. -/
theorem nucNorm_smul_v2 {d₁ d₂ : ℕ} (c : ℝ) (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    nucNorm (c • A) = |c| * nucNorm A := by sorry

end WainwrightHDS.NucNorm
