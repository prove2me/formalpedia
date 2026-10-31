-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_exists_top_r_singular_subspaces
-- name    : WainwrightHDS.NucNorm.exists_top_r_singular_subspaces
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T04:05:59.652253+00:00
-- url     : https://prove2.me/theorems/2c8c1fae-4daa-4722-ab76-a07db3bdace9
-- title:
--   Existence of top-$r$ singular subspaces for $\Theta^*$
-- statement:
--   For any matrix $\Theta^* \in \mathbb{R}^{d_1 \times d_2}$ and integer $1 \le r \le \min(d_1, d_2)$, choosing $U \subseteq \mathbb{R}^{d_1}$ and $V \subseteq \mathbb{R}^{d_2}$ to be the spans of the top-$r$ left and right singular vectors of $\Theta^*$ yields subspaces of dimension at most $r$ such that the residual nuclear norm satisfies $\|\Theta^*_{\mathcal{M}^\perp}\|_{\mathrm{nuc}} \le \sum_{j=r}^{\min(d_1,d_2)-1} \sigma_j(\Theta^*)$, the perturbation projection $\Delta_{\overline{\mathcal{M}}}$ lies in $\overline{\mathcal{M}}(U, V)$, and $\|\Delta_{\overline{\mathcal{M}}}\|_F^2 \le \|\Delta\|_F^2$.
-- source:
--   Wainwright, High-Dimensional Statistics (2019), Section 10.2.2, p. 320

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_Mspace
import Definitions.Def_WainwrightHDS_NucNorm_Mbar
import Definitions.Def_WainwrightHDS_NucNorm_MbarPerp
import Definitions.Def_WainwrightHDS_NucNorm_projMat
import Definitions.Def_WainwrightHDS_NucNorm_projM
import Definitions.Def_WainwrightHDS_NucNorm_projMperp
import Definitions.Def_WainwrightHDS_NucNorm_projMbar
import Definitions.Def_WainwrightHDS_NucNorm_projMbarPerp

namespace WainwrightHDS.NucNorm

theorem exists_top_r_singular_subspaces {d₁ d₂ : ℕ} (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂) :
    ∃ (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))),
      Module.finrank ℝ U ≤ r ∧ Module.finrank ℝ V ≤ r ∧
      nucNorm (projMperp U V Θstar) ≤ ∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar ∧
      (∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ, projMbar U V Δ ∈ Mbar U V) ∧
      (∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ, frobSq (projMbar U V Δ) ≤ frobSq Δ) := by sorry

end WainwrightHDS.NucNorm
