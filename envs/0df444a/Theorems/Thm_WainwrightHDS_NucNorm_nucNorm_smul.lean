-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_smul
-- name    : WainwrightHDS.NucNorm.nucNorm_smul
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T01:31:29.042837+00:00
-- url     : https://prove2.me/theorems/01e66266-5331-4736-99b8-407ffbbcbbde
-- title:
--   Absolute homogeneity of the nuclear norm
-- statement:
--   For any scalar $c \in \mathbb{R}$ and any $d_1 \times d_2$ real matrix $A$, the nuclear norm satisfies $\|c A\|_{\mathrm{nuc}} = |c| \, \|A\|_{\mathrm{nuc}}$.

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

namespace WainwrightHDS.NucNorm

/-- **Absolute homogeneity of the nuclear norm**: `|||c • A|||_nuc = |c| · |||A|||_nuc`. -/
theorem nucNorm_smul {d₁ d₂ : ℕ} (c : ℝ) (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    nucNorm (c • A) = |c| * nucNorm A := by sorry

end WainwrightHDS.NucNorm
