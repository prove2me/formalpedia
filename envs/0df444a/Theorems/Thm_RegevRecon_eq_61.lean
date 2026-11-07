-- Prove2me | Theorems.Thm_RegevRecon_eq_61
-- name    : RegevRecon.eq_61
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:39.877184+00:00
-- url     : https://prove2.me/theorems/61ac79f6-6f9b-4345-afe5-283ff634dcf9
-- title:
--   (61) — the Fourier identities
-- statement:
--   Write $\hat q(b)=\sum_aq_a\omega^{ab}$ and $m_\ell(b)=E[|\hat q^{(\ell)}(b)|^2]$. Parseval's identity, the root convolution and independence of its $k$ inputs give
--
--   $$
--   \Psi_\ell=\frac1p\sum_{b\ne0}m_\ell(b),\qquad E\bigl[\|\mu_{\mathrm{root}}^{(\ell)}-u\|_2^2\bigr]=\frac1p\sum_{b\ne0}|\hat\mu(b)|^2m_\ell(b)^k.
--   $$
--
--   These identities reduce the threshold equality to the nonvanishing of $\hat\mu(b)$.
--
--   Differences from the source:
--   - encoding: laws of random vectors, =d → finitely supported Law; =d is equality of masses at every whole vector; reason: all these vectors take finitely many values; same instances
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), (61), pp.23–24

import Mathlib
import Definitions.Def_RegevRecon_qLaw
import Definitions.Def_RegevRecon_etaLaw

namespace RegevRecon

open Filter Topology

/-- **The Fourier identities (61)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.24: `Ψ_ℓ = (1/p) Σ_{b≠0} m_ℓ(b)` and
`E[‖μ_root^(ℓ) − u‖₂²] = (1/p) Σ_{b≠0} |μ̂(b)|² m_ℓ(b)^k`, with `q̂(b) = Σ_a q_a ω^{ab}` and
`m_ℓ(b) = E[|q̂^(ℓ)(b)|²]` (p.23). -/
theorem eq_61 {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ)
    (β : ℝ) (hβ : 0 ≤ β) (ℓ : ℕ) :
    Psi k D S Λ β ℓ =
        (p : ℝ)⁻¹ * ∑ b ∈ Finset.univ.filter (· ≠ (0 : ZMod p)), secondMoment k D S Λ β ℓ b ∧
      (rootLaw k D S Λ β ℓ).expect distSq =
        (p : ℝ)⁻¹ * ∑ b ∈ Finset.univ.filter (· ≠ (0 : ZMod p)),
          ‖fourier (channel S β) b‖ ^ 2 * secondMoment k D S Λ β ℓ b ^ k := by sorry

end RegevRecon
