-- Prove2me | Theorems.Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_multiplicativeReduction
-- name    : WeierstrassCurve.galoisRepUnramifiedAt_of_multiplicativeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/22395be2-8415-5f36-b569-d8b398666dec
-- title:
--   Multiplicative reduction with ℓ ∣ v_q(Δ): ℓ-torsion unramified at q
-- statement:
--   Let $W$ be a Weierstrass equation with coefficients in $\mathbb{Z}$, and let $q$ and $\ell$ be natural numbers. Assume: $q$ is prime; $\ell$ is prime; $\ell \neq q$; the discriminant $\Delta(W)$ is nonzero; $q \mid \Delta(W)$ in $\mathbb{Z}$; $q \nmid c_4(W)$; and $\ell$ divides `padicValInt q W.Δ`, the exponent of $q$ in $\Delta(W)$. The conclusion is the project's predicate `GaloisRepUnramifiedAt` for the base change $W_{\mathbb{Q}} =$ `W.map (Int.castRingHom ℚ)`, with ambient field the algebraic closure $\overline{\mathbb{Q}}$, base field $\mathbb{Q}$, torsion level $\ell$ and prime $q$; unfolded, this says: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ that lies over $q$ in the project's sense (namely $q$, viewed in $\overline{\mathbb{Q}}$, belongs to `A.nonunits`), for every $\sigma$ in `A.inertiaSubgroupIn ℚ` — the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of the decomposition subgroup of $A$ — and for every element $x$ of the $\mathbb{Z}$-submodule `Submodule.torsionBy ℤ` of the affine points of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$ killed by $\ell$, one has $\sigma \bullet x = x$, the action being the one induced by functoriality of points along the field automorphism $\sigma$. Note that minimality of the model, the elliptic-curve hypothesis and any smoothness assumption are not imposed: the hypotheses are exactly the divisibility conditions $q \mid \Delta$, $q \nmid c_4$, $\Delta \neq 0$ together with $\ell \mid v_q(\Delta)$.
--
--   Classically this is the 'if' direction of Proposition 2.12(c) of Darmon–Diamond–Taylor: for a curve with multiplicative reduction at $q$, the mod-$\ell$ representation is unramified at $q$ as soon as $\ell$ divides the valuation of the minimal discriminant, the standard proof going through the Tate parametrisation $E \cong \mathbb{G}_m/t^{\mathbb{Z}}$ with $v_q(t) = v_q(\Delta_{\min})$. The formal statement differs in shape: multiplicative reduction is encoded by the divisibility conditions $q \mid \Delta(W)$, $q \nmid c_4(W)$ on a fixed integral model (the condition appearing in the project's `IsSemistableModel`), the discriminant valuation is that of the given model, and unramifiedness is quantified over all valuation subrings of $\overline{\mathbb{Q}}$ lying over $q$ and over their inertia subgroups, rather than over a chosen embedding into $\overline{\mathbb{Q}}_q$. It is the input to [`FreyPackage.freyGaloisRep_isUnramifiedAt`](thm.html#FreyPackage.freyGaloisRep_isUnramifiedAt), which applies it to the Frey curve at the odd primes $q \neq p$, where the exponent of $q$ in the discriminant is divisible by $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_multiplicativeReduction.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.galoisRepUnramifiedAt_of_multiplicativeReduction (W : WeierstrassCurve ℤ) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hΔ : W.Δ ≠ 0) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hv : ℓ ∣ padicValInt q W.Δ) : WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) ℓ q := by sorry
