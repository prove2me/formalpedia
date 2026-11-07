-- Prove2me | Theorems.Thm_RegevRecon_eq_62
-- name    : RegevRecon.eq_62
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:37.980715+00:00
-- url     : https://prove2.me/theorems/fd879fa2-cf0e-4463-b23e-1cc652459a9f
-- title:
--   (62) — vanishing error iff vanishing excess
-- statement:
--   For every $\beta\ge0$,
--
--   $$
--   \lim_{\ell\to\infty}P_{\mathrm{err}}^{(\ell)}=0\iff\Psi_\infty=0.
--   $$
--
--   Since $P_{\mathrm{err}}$ is continuous and vanishes only at $u$, compactness of the simplex relates the error to $\|\mu_{\mathrm{root}}^{(\ell)}-u\|_2$, and (61) relates that norm to $\Psi_\ell$. Together with (54), this gives the threshold equality.
--
--   Differences from the source:
--   - encoding: thresholds with inf ∅ = ∞ and lim > 0 → thresholds in ℝ≥0∞; lim > 0 is ¬Tendsto · atTop (𝓝 0); reason: for a nonnegative sequence with a limit the two agree, and the limits exist by milestones
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), (62), p.24

import Mathlib
import Definitions.Def_RegevRecon_qLaw
import Definitions.Def_RegevRecon_etaLaw

namespace RegevRecon

open Filter Topology

/-- **Vanishing error iff vanishing excess (62)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.24: `lim_{ℓ→∞} P_err^(ℓ) = 0 ⟺ Ψ_∞ = 0`, for
every `β ≥ 0` (at `β = 0`, `μ = u`, and both conditions hold directly). -/
theorem eq_62 {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ)
    (β : ℝ) (hβ : 0 ≤ β) :
    Tendsto (perr k D S Λ β) atTop (𝓝 0) ↔ Tendsto (Psi k D S Λ β) atTop (𝓝 0) := by sorry

end RegevRecon
