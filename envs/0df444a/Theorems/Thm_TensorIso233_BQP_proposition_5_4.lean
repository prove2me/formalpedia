-- Prove2me | Theorems.Thm_TensorIso233_BQP_proposition_5_4
-- name    : TensorIso233.BQP.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:33.916292+00:00
-- url     : https://prove2.me/theorems/10edcbfb-f44e-48a2-a747-f08976051c5d
-- title:
--   Proposition 5.4 — one integer linear system and one congruence
-- statement:
--   Let $(A,B)$ and $(A',B')$ be pairs of the form (5.6) with the same $a,d,c>0$ and the same $e,g$ (the primed pair has entries $p',q',r',h'$), as after a fixed sign choice on p. 23. Call them equivalent when $P(A+tB)=A'Q$ and $PB=B'Q$ for some $t\in\mathbb Z$ and upper unitriangular integer $P,Q$. With $K,b$ from (5.14), $r_1$ from (5.15), $\Psi$ from (5.16), $L=\ker_{\mathbb Z}K$ and $\eta=\gcd(\gcd(a,c),\Psi(\ell_1),\dots,\Psi(\ell_m))$ from (5.17):
--
--   1. the pairs are equivalent if and only if $K\xi=b$ has an integer solution and, for **every** integer solution $\xi_0$ and every finite family $\ell_1,\dots,\ell_m$ spanning $L$,
--   $$
--   r'-r_1\equiv0\pmod\eta ; \tag{5.18}
--   $$
--   2. equivalently, if and only if (5.18) holds for **some** integer solution $\xi_0$ and some spanning family.
--
--   Thus equivalence is decided by one integer linear system and one congruence, and the test does not depend on the choices. No division by $e$ or $g$ occurs, so they may vanish.
--
--   Differences from the source:
--   - reading: equivalence is decided by one integer linear system and one congruence → the exact criterion (5.18): solvability of Kξ = b together with η ∣ r′ − r₁, in a for-all form and an exists form; reason: the proof on pp. 24–25 proves precisely this criterion
--   - generalization: two adapted pairs (flag-adapted, of shape (5.6)) → any two pairs of shape (5.6) with matching a, d, c, e, g; reason: the criterion uses only the matrix shapes and unitriangularity; adapted pairs, including after the sign relabelling, have this shape
--   - generalization: an integral basis ℓ₁, …, ℓₘ of L → any finite family spanning L; reason: every basis spans; η is the gcd of ρ with generators of the image of Ψ mod ρ, so any generating family gives the same η
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), Proposition 5.4, p. 24, (5.14)–(5.17), and the criterion (5.18), p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Definitions.Def_TensorIso233_BQP_PureCube

open scoped Matrix

namespace TensorIso233.BQP

/-- Proposition 5.4 (p. 24) in the exact form (5.18) proved on pp. 24–25: for two pairs of the
form (5.6) with the same `a, d, c > 0` and the same `e, g`, the pairs are equivalent by an
integral shear and upper-unitriangular `P, Q` iff the integer system (5.14) `Kξ = b` is
solvable and `η ∣ r' − r₁`; the congruence holds for every solution `ξ₀` and every spanning
family of `L = ker_ℤ K` as soon as it holds for one. -/
theorem proposition_5_4 (a p r d q c e h g p' r' q' h' : ℤ) (ha : 0 < a) (hd : 0 < d) (hc : 0 < c) :
    (UnitriEquiv (shape56 a p r d q c e h g) (shape56 a p' r' d q' c e h' g) ↔
      (∃ ξ : Fin 5 → ℤ, Kmat a d c e g *ᵥ ξ = bvec p q h p' q' h') ∧
      ∀ ξ₀ : Fin 5 → ℤ, Kmat a d c e g *ᵥ ξ₀ = bvec p q h p' q' h' →
        ∀ (m : ℕ) (ℓ : Fin m → Fin 5 → ℤ), Submodule.span ℤ (Set.range ℓ) = kerZ a d c e g →
          (eta a c h' q' p' g ℓ : ℤ) ∣ r' - r1 r h q g p' ξ₀) ∧
    (UnitriEquiv (shape56 a p r d q c e h g) (shape56 a p' r' d q' c e h' g) ↔
      ∃ ξ₀ : Fin 5 → ℤ, Kmat a d c e g *ᵥ ξ₀ = bvec p q h p' q' h' ∧
        ∃ (m : ℕ) (ℓ : Fin m → Fin 5 → ℤ), Submodule.span ℤ (Set.range ℓ) = kerZ a d c e g ∧
          (eta a c h' q' p' g ℓ : ℤ) ∣ r' - r1 r h q g p' ξ₀) := by sorry

end TensorIso233.BQP
