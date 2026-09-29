-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two
-- name    : WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/ddb77d49-a8c8-5ce7-8a6c-ff404cfb347c
-- title:
--   Supersingular curves admit a deformation moving the q-th [q]-coefficient
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $k$ be a field of characteristic $q$, and let $E_0$ be a Weierstrass curve over $k$ which is elliptic (`IsElliptic`). Assume that the formal group `E₀.formalGroup` of $E_0$ — the formal group whose underlying two-variable series is `E₀.formalGroupLawFixed`, the formal group law of the Weierstrass curve in the standard parameter — satisfies the predicate [`FormalGroup.IsDrinfeldBasisAdic ⊥ q 0 0`](def/FormalGroup_DrinfeldBasis.html#L46), that is: with respect to the zero ideal of $k$ there is a unit power series $u$ with `E₀.formalGroup.nthSeries q` $= u \cdot$ `drinfeldDivisor q 0 0`, where `nthSeries` is the multiplication-by-$n$ series defined recursively by `nthSeries 0 = 0` and `nthSeries (n+1)` $=$ the substitution of (`nthSeries n`, $X$) into the group law. The conclusion asserts the existence of a Weierstrass curve $E_1$ over the dual numbers $k[\varepsilon]$, $\varepsilon^2 = 0$, such that the coefficientwise image of $E_1$ under the ring homomorphism $k[\varepsilon] \to k$ killing $\varepsilon$ equals $E_0$, and such that for every formal group $G$ over $k[\varepsilon]$ whose underlying power series is `E₁.formalGroupLawFixed`, the $\varepsilon$-component (`TrivSqZeroExt.snd`) of the coefficient of $X^q$ in `G.nthSeries q` is nonzero. Quantifying over all such $G$ avoids asserting ellipticity of $E_1$ over the non-domain $k[\varepsilon]$.
--
--   By the cited equivalence [`FormalGroup.isDrinfeldBasisAdic_zero_zero_iff`](thm.html#FormalGroup.isDrinfeldBasisAdic_zero_zero_iff), the hypothesis on $E_0$ says that $[q]$ on its formal group is a unit times $Z^{q^2}$, i.e. the formal group has height two and $E_0$ is supersingular; the conclusion is the nondegeneracy statement that the $Z^q$-coefficient of $[q]$, equivalently the Hasse invariant, has a simple zero at a supersingular point in some Weierstrass direction (Igusa; first-order Serre–Tate). It feeds the construction of Drinfeld-basis lifts used downstream, via [`WeierstrassCurve.exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries_of_ne_two`](thm.html#WeierstrassCurve.exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries_of_ne_two) and [`WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero`](thm.html#WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0) :
    ∃ E₁ : WeierstrassCurve (DualNumber k),
      E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      ∀ G : FormalGroup (DualNumber k), G.toPowerSeries = E₁.formalGroupLawFixed →
        TrivSqZeroExt.snd (PowerSeries.coeff q (G.nthSeries q)) ≠ 0 := by sorry
