-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot
-- name    : WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/5bc35e85-561a-5cf5-a679-502ae8aa7daa
-- title:
--   Formal-group isomorphisms of congruent lifts come from variable changes
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $k$ be a field of characteristic $q$, and let $E_0$ be an elliptic Weierstrass curve over $k$ whose formal group $F_0 = E_0$`.formalGroup` satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`: taking the ideal $\bot$ as the ambient ideal, there is a unit power series $u$ with $F_0$`.nthSeries q` $= u \cdot F_0$`.drinfeldDivisor q 0 0`. Let $T$ be a local commutative ring and $I \subseteq T$ an ideal with $I \cdot \mathfrak{m}_T = 0$ and $I \subseteq \mathfrak{m}_T$, and let $\mathrm{res}_T : T \to k$ be a surjective ring homomorphism with kernel $\mathfrak{m}_T$. Let $E, E'$ be Weierstrass curves over $T$ with $E$ reducing to $E_0$ along $\mathrm{res}_T$ and with $E'$ and $E$ having the same reduction modulo $I$. Let $G, G'$ be formal groups over $T$ whose underlying two-variable power series are `E.formalGroupLawFixed` and `E'.formalGroupLawFixed` respectively, and let $\psi$ be a `LawIso` from $G$ to $G'$, that is, a power series with zero constant term, with unit linear coefficient, intertwining the two group laws, and assume every coefficient of $\psi$ is congruent modulo $I$ to the corresponding coefficient of $X$ (the coefficient of $X$ lies in $1 + I$, all others in $I$). Then there is a Weierstrass variable change $C$ over $T$ whose reduction modulo $I$ is the identity variable change and with $C \bullet E = E'$.
--
--   This is the uniqueness (rigidity) step of the Serre–Tate deformation argument in the supersingular case, in Weierstrass coordinates: over a small thickening, a $\star$-isomorphism between the formal groups of two lifts that agree modulo $I$ is induced by a change of variables congruent to the identity modulo $I$. It is used by [`WeierstrassCurve.exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso`](thm.html#WeierstrassCurve.exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso) and by [`WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot_of_prime`](thm.html#WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot_of_prime), which propagate it along a tower of such thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E E' : WeierstrassCurve T) (hE : E.map resT = E₀)
    (hEE' : E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I))
    (G : FormalGroup T) (hG : G.toPowerSeries = E.formalGroupLawFixed)
    (G' : FormalGroup T) (hG' : G'.toPowerSeries = E'.formalGroupLawFixed)
    (ψ : FormalGroup.LawIso G G')
    (hψ : ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈ I) :
    ∃ C : WeierstrassCurve.VariableChange T, C.map (Ideal.Quotient.mk I) = 1 ∧ C • E = E' := by sorry
