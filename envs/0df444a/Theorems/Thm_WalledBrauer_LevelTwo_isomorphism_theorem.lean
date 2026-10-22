-- Prove2me | Theorems.Thm_WalledBrauer_LevelTwo_isomorphism_theorem
-- name    : WalledBrauer.LevelTwo.isomorphism_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:03.376766+00:00
-- url     : https://prove2.me/theorems/bf158b07-4ab8-472d-b999-52b11f7a9864
-- title:
--   Theorem 6.2 — explicit walled Brauer corner isomorphism
-- statement:
--   Let $r,t\ge0$, let $m,n$ be positive integers with $m,n\ge r+t$, and let $\delta\in\mathbb Z$ satisfy Assumption 5.5. Let $A=\mathbb V\operatorname{Br}^{\mathrm{cycl}}_{r,t}$ have the parameters of (5.4), and let $f$ be the spectral truncation of Definition 5.6. For every allowed family of polynomial square roots in (6.2), the assignments of (6.5) extend to a multiplicative complex-linear map
--   $$\Phi:\operatorname{Br}_{r,t}(-\delta)\longrightarrow A,\qquad \Phi(1)=f.$$
--   It sends $1_a$ to $f1_a$ and the four local crossing and contraction generators to $\sigma_k1_a,\widehat\sigma_k1_a,\tau_k1_a,\widehat\tau_k1_a$ respectively. Moreover $\Phi$ is injective and
--   $$\operatorname{range}(\Phi)=fAf.$$
--
--   Thus the source algebra is isomorphic to the full idempotent corner of the cyclotomic algebra. **Formalization Note** Lean uses zero-based positions, and requires $m,n\ge r+t$ explicitly because the proof invokes Theorem 5.2 under that hypothesis. The map is specified in the ambient algebra with a range equality, which is the literal meaning of an isomorphism onto $fAf$.
-- source:
--   Sartori and Stroppel, Walled Brauer algebras as idempotent truncations of level 2 cyclotomic quotients, arXiv:1411.2771v2, p. 13, Theorem 6.2, (6.5); p. 15, proof

import Mathlib
import Definitions.Def_WalledBrauer_LevelTwo_Setting

namespace WalledBrauer.LevelTwo

/-- Theorem 6.2, p. 13. The codomain is the full cyclotomic algebra so the
range clause identifies exactly the corner `f A f`. -/
theorem isomorphism_theorem {r t m n : ℕ} {δ : ℤ}
    (hm : 0 < m) (hn : 0 < n) (hmn : r + t ≤ m ∧ r + t ≤ n)
    (h55 : Assumption55 r t m n δ)
    (R : Fin (r + t) → A r t m n δ) (hR : IsRootFamily δ R) :
    ∃ Φ : Br r t (-(δ : ℂ)) →ₗ[ℂ] A r t m n δ,
      (∀ x y, Φ (x * y) = Φ x * Φ y) ∧
      Φ 1 = f δ ∧
      (∀ a : Orientation r t, Φ (brId (-(δ : ℂ)) a) = fAt δ a) ∧
      (∀ (k : Fin (r + t)) (hk : k.val + 1 < r + t) (a : Orientation r t),
        Φ (brAtom (-(δ : ℂ)) .s k a) = sigma δ R k hk a ∧
        Φ (brAtom (-(δ : ℂ)) .sh k a) = sigmaHat δ R k hk a ∧
        Φ (brAtom (-(δ : ℂ)) .e k a) = tau δ R k hk a ∧
        Φ (brAtom (-(δ : ℂ)) .eh k a) = tauHat δ R k hk a) ∧
      Function.Injective Φ ∧
      (∀ x : A r t m n δ, x ∈ LinearMap.range Φ ↔ f δ * x * f δ = x) := by sorry

end WalledBrauer.LevelTwo
