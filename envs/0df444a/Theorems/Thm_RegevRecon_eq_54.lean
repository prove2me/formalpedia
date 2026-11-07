-- Prove2me | Theorems.Thm_RegevRecon_eq_54
-- name    : RegevRecon.eq_54
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:50.528964+00:00
-- url     : https://prove2.me/theorems/55f62848-a1cd-4360-99ad-3de859d90d8c
-- title:
--   (54) — the law identities between the two recursions
-- statement:
--   Fix a prime $p$, integers $3\le k<D$, a nonempty proper $S\subsetneq\mathbb F_p$ and an exchangeable law $\Lambda$ on $(\mathbb F_p^\times)^D$. For every finite $\beta\ge0$ and depth $\ell\ge0$,
--
--   $$
--   \tilde\eta^{(\ell)}\overset d=\mathcal L(q^{(\ell)}),\qquad\Psi_\ell=E\bigl[\|q^{(\ell)}-u\|_2^2\bigr],\qquad u=(1/p,\dots,1/p).
--   $$
--
--   So the reconstruction message is exactly the lift of the BPQM message, and the excess of reconstruction measures the distance of the BPQM message from uniform.
--
--   Differences from the source:
--   - encoding: laws of random vectors, =d → finitely supported Law; =d is equality of masses at every whole vector; reason: all these vectors take finitely many values; same instances
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), Theorem 4, (54), p.21; proof p.23

import Mathlib
import Definitions.Def_RegevRecon_qLaw
import Definitions.Def_RegevRecon_etaLaw

namespace RegevRecon

open Filter Topology

/-- **The law identities (54)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), Theorem 4, p.21, proof p.23: for every finite `β ≥ 0` and depth
`ℓ ≥ 0`, `η̃^(ℓ) =d 𝓛(q^(ℓ))` and `Ψ_ℓ = E[‖q^(ℓ) − u‖₂²]`. -/
theorem eq_54 {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ)
    (β : ℝ) (hβ : 0 ≤ β) (ℓ : ℕ) :
    etaLaw k D S Λ β ℓ = liftLaw (qLaw k D S Λ β ℓ) ∧
      Psi k D S Λ β ℓ = (qLaw k D S Λ β ℓ).expect distSq := by sorry

end RegevRecon
