-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_add_le
-- name    : WainwrightHDS.NucNorm.nucNorm_add_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T01:31:20.070044+00:00
-- url     : https://prove2.me/theorems/260a12aa-4eed-4fe1-a913-d85ff6c09051
-- title:
--   Triangle inequality for the nuclear norm
-- statement:
--   For any two $d_1 \times d_2$ real matrices $A$ and $B$, the nuclear norm satisfies the triangle inequality $\|A + B\|_{\mathrm{nuc}} \le \|A\|_{\mathrm{nuc}} + \|B\|_{\mathrm{nuc}}$.

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

namespace WainwrightHDS.NucNorm

/-- **Triangle inequality for the nuclear norm**: `|||A + B|||_nuc ≤ |||A|||_nuc + |||B|||_nuc`. -/
theorem nucNorm_add_le {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    nucNorm (A + B) ≤ nucNorm A + nucNorm B := by sorry

end WainwrightHDS.NucNorm
