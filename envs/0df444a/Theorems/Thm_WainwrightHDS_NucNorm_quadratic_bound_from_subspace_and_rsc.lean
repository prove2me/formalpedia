-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_quadratic_bound_from_subspace_and_rsc
-- name    : WainwrightHDS.NucNorm.quadratic_bound_from_subspace_and_rsc
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T04:05:56.563105+00:00
-- url     : https://prove2.me/theorems/77fe0bf8-a0a2-4293-a7dd-094388283406
-- title:
--   Quadratic Frobenius bound from top-$r$ singular subspace and RSC
-- statement:
--   Given subspaces $U \subseteq \mathbb{R}^{d_1}$ and $V \subseteq \mathbb{R}^{d_2}$ of dimension at most $r$ satisfying the tail bound $\|\Theta^*_{\mathcal{M}^\perp}\|_{\mathrm{nuc}} \le \sum_{j=r}^{\min(d_1,d_2)-1} \sigma_j(\Theta^*)$ and subspace compatibility $\|\Delta_{\overline{\mathcal{M}}}\|_{\mathrm{nuc}} \le \sqrt{2r}\|\Delta\|_F$ for $\Delta = \widehat{\Theta} - \Theta^*$, combining the basic inequality, restricted strong convexity, and the nuclear-norm cone constraint under $128 c_0 (d_1 + d_2) r \le \kappa n$ yields the quadratic Frobenius error inequality.
-- source:
--   Wainwright, High-Dimensional Statistics (2019), Proof of Proposition 10.6, p. 320

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_obsOp
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_lsNucObjective
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

theorem quadratic_bound_from_subspace_and_rsc {n d₁ d₂ : ℕ}
    (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ) (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (w y : Fin n → ℝ) (hy : ∀ i, y i = obsOp X Θstar i + w i)
    (κ c₀ lam : ℝ) (hκ : 0 < κ) (hc₀ : 0 < c₀) (hlam : 0 < lam)
    (hRSC : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ,
      1 / (2 * (n : ℝ)) * ∑ i, (obsOp X Δ i) ^ 2 ≥
        κ / 2 * frobSq Δ - c₀ * (((d₁ : ℝ) + d₂) / n) * nucNorm Δ ^ 2)
    (hG : opNorm2 ((1 / (n : ℝ)) • ∑ i, w i • X i) ≤ lam / 2)
    (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, lsNucObjective X y lam Θhat ≤ lsNucObjective X y lam Θ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂)
    (hrκ : 128 * c₀ * ((d₁ : ℝ) + d₂) * r ≤ κ * n)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (hU : Module.finrank ℝ U ≤ r) (hV : Module.finrank ℝ V ≤ r)
    (h_tail : nucNorm (projMperp U V Θstar) ≤ ∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar)
    (h_mbar_bound : nucNorm (projMbar U V (Θhat - Θstar)) ≤
      Real.sqrt (2 * (r : ℝ)) * Real.sqrt (frobSq (Θhat - Θstar))) :
    κ * frobSq (Θhat - Θstar) ≤
      3 / 2 * lam * Real.sqrt (2 * r) * Real.sqrt (frobSq (Θhat - Θstar)) +
        lam * (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) +
        16 * c₀ * ((d₁ : ℝ) + d₂) / n *
          (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) ^ 2 := by sorry

end WainwrightHDS.NucNorm
