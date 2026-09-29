-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero
-- name    : WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/e3c5dbfc-351e-51f2-8ca9-db0d5c915686
-- title:
--   Deformation moving the Z^q-coefficient of [q]
-- statement:
--   Fix a prime $q$, a field $k$ of characteristic $q$, and a Weierstrass curve $E_0$ over $k$ that is elliptic (invertible discriminant). The hypothesis on $E_0$ is `IsDrinfeldBasisAdic` for the zero ideal $\bot$, the integer $q$ and the parameters $0,0$: taking $\bot$ as the designated ideal of $k$, there exists a power series $u \in k[\![Z]\!]$ which is a unit such that the $q$-th iterate series $[q]$ of the formal group $\widehat{E_0}$ attached to $E_0$ — the series `nthSeries` obtained from the zero series by repeatedly substituting $(\,\cdot\,, Z)$ into the formal group law `formalGroupLawFixed` of $E_0$ — equals $u$ times `drinfeldDivisor q 0 0`. The conclusion asserts the existence of a Weierstrass curve $E_1$ over the dual numbers $k[\varepsilon] =$ `DualNumber k` (no ellipticity of $E_1$ is demanded) such that, first, the base change of $E_1$ along the projection $k[\varepsilon] \to k$ onto the first component is $E_0$, and, second, for every formal group $G$ over $k[\varepsilon]$ whose underlying two-variable power series is the formal group law `formalGroupLawFixed` of $E_1$, the $\varepsilon$-component of the coefficient of $Z^q$ in the $q$-th iterate series of $G$ is nonzero.
--
--   The coefficient of $Z^q$ in $[q]$ of the formal group of a Weierstrass curve in characteristic $q$ is its Hasse invariant up to a unit, so this is the classical statement — Igusa's theorem, Katz–Mazur 12.4 — that at a supersingular point the Hasse invariant vanishes to order exactly one in a suitable Weierstrass direction, equivalently first-order Serre–Tate. It removes the restriction $q \neq 2$ present in [`WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two`](thm.html#WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two), and feeds [`WeierstrassCurve.exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries`](thm.html#WeierstrassCurve.exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0) :
    ∃ E₁ : WeierstrassCurve (DualNumber k),
      E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      ∀ G : FormalGroup (DualNumber k), G.toPowerSeries = E₁.formalGroupLawFixed →
        TrivSqZeroExt.snd (PowerSeries.coeff q (G.nthSeries q)) ≠ 0 := by sorry
