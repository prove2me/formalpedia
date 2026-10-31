-- Prove2me | Theorems.Thm_ScalarMultiRisk_proposition_4_6
-- name    : ScalarMultiRisk.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:44.256352+00:00
-- url     : https://prove2.me/theorems/27f37323-dcd8-4b65-826a-14fc12fb6962
-- title:
--   Proposition 4.6 (corrected: positive homogeneity holds on $\{\lambda>0\}\cup\{\pi^S_t(0)>-\infty\}$) — properties of $\pi^S_t$
-- statement:
--   Let $S\in\mathcal S$ satisfy (NA) and let $t$ be a time. Then:
--
--   1. (conditional cash invariance) $\pi^S_t(X+m)=\pi^S_t(X)-S_t^{\mathsf T}m$ for $X\in L^\infty(\mathbb R^d)$, $m\in L^\infty_t(\mathbb R^d)$;
--   2. (monotonicity) $\pi^S_t(X)\le\pi^S_t(Y)$ if $S_T^{\mathsf T}X\ge S_T^{\mathsf T}Y$ almost surely;
--   3. (conditional convexity) $\pi^S_t(\lambda X+(1-\lambda)Y)\le\lambda\pi^S_t(X)+(1-\lambda)\pi^S_t(Y)$ for every $\lambda\in L^\infty_t([0,1])$;
--   4. (value consistency) $\pi^S_t(X)=\pi^S_t([S_T^{\mathsf T}X]e_1)$.
--
--   If $A_t$ is a conditional cone, then for every $\lambda\in L^\infty_t(\mathbb R_+)$,
--
--   $$\pi^S_t(\lambda X)=\lambda\pi^S_t(X)\quad\text{a.s. on }\{\lambda>0\}\cup\{\pi^S_t(0)>-\infty\}.$$
--
--   These properties say that $\pi^S_t$ depends on a portfolio only through its value at prices $S_T$, and they are what reduces $\pi^S_t$ to a univariate risk measure.
--
--   Differences from the source:
--   - correction: if $A_t$ is a conditional cone then $\pi^S_t$ is conditionally positively homogeneous → the identity holds a.s. on $\{\lambda>0\}\cup\{\pi^S_t(0)>-\infty\}$; reason: with $0\cdot(-\infty)=0$ the printed identity fails at $\lambda=0$: on one point, $T=1$, $d=2$, $K_0=K_1=\{x_1+x_2\ge0,\ x_1+2x_2\ge0\}$, $\rho_0(X)=\max(-X_1-1.2X_2,-X_1-1.5X_2)$, $\rho_1(X)=-X_1-1.2X_2$, $S\equiv(1,1.8)$ gives $\pi^S_0\equiv-\infty$, so $\pi^S_0(0\cdot X)=-\infty\ne0$
--   - encoding: Assumption 3.3 assumes a set-valued $R_t$ with $\rho_t$ from (3.1) and $A_t=\{X\mid 0\in R_t(X)\}$ → hypothesis `StandingAssumptions` on $\rho_t$ with $A_t=\{X\mid\rho_t(X)\le0$ a.s.$\}$; reason: Theorem 3.2 gives $R_t(X)=(\rho_t(X)+L^\infty_t(\mathbb R_+))e_1$, so the two formulations have the same instances
--   - encoding: random vectors are a.e.-classes → functions on $\Omega$, with a.e. (in)equalities; reason: same content; every set involved is closed under a.e. modification
--   - reading: time is written $(\mathcal F_t)_{t=0}^T$, with a stray "$[0,T]$" on p.30 → discrete time $t\in\{0,\dots,T\}$; reason: every construction sums over $s=t,\dots,T$
--   - encoding: $\pi^S_t$ takes values in $L^0_t(\mathbb R)\cup\{-\infty\}$ → extended real values; reason: Lean convention; same instances
--   - reading: “$\mathcal F_s$-measurable random convex cones $K_s$” (p.7), the solvency cones of Assumption 3.3, and the convex cone $\bar K$ → each $K_s(\omega)$ and $\bar K$ is a convex cone containing $0$ (`PointedCone`), and $\{(\omega,x)\mid x\in K_s(\omega)\}$ is $\mathcal F_s\otimes\mathfrak B(\mathbb R^d)$-measurable; no closedness and no $\mathbb R^d_+\subseteq K_s$ is assumed; reason: the paper does not define random cones; graph measurability is the standard notion (Molchanov); solvency cones contain $0$, and the paper uses $0\in\mathbb K_t$ (Theorem 3.2 and after (3.1))
--   - encoding: a filtered probability space satisfying the usual conditions with $\mathcal F_0$ trivial and $\mathcal F=\mathcal F_T$ → $\mathcal F_T$ is the ambient σ-algebra, every $\mathcal F_0$-set has probability $0$ or $1$, and “$\mathcal F_t$-measurable” is a.e. strong measurability for $\mathcal F_t$; reason: in discrete time the usual conditions say that $\mathcal F_0$ contains the null sets, so the $\mathcal F_t$-measurable classes are the same
--   - encoding: asset $i$, $i=1,\dots,d$, with cash $e_1=(1,0,\dots,0)^{\mathsf T}$ → index $i-1$ of `Fin d` with `[NeZero d]`; $e_1$ is the published `QKPSDP.e1 d` (`Pi.single 0 1`); reason: Lean indices start at $0$; same instances
--   - encoding: $\mathbb E^{\mathbb Q}[\cdot\mid\mathcal F_t]$, the $\mathbb P$-a.s. version defined through the density process (p.6) → Mathlib's conditional expectation `Q[·|F t]` under $\mathbb Q$; reason: only $\mathbb Q\sim\mathbb P$ occur, and then the two agree a.s.
--   - encoding: $\|e_i\|_{\mathbb K_T,0}$, an essential infimum over $c\in L^\infty_0(\mathbb R)$ (3.3), and $\mathcal Q^e(S)=\{\mathbb Q\in\mathcal M\mid(\mathbb Q,S)\in\mathcal Q^e_0\}$ → the real infimum over constants $c$ with $ce_1-e_i,\ e_i+ce_1\in K_T$ a.s.; `Qe` lists only the conditions of $\mathcal Q_0$ not already in (4.3); reason: $\mathcal F_0$ is trivial and the set of such $c$ is nonempty and contained in $[0,\infty)$ under the standing assumptions; every statement takes $S\in\mathcal S$
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proposition 4.6, p.20

import Mathlib
import Definitions.Def_ScalarMultiRisk_StandingAssumptions
import Definitions.Def_ScalarMultiRisk_priceSet
import Definitions.Def_ScalarMultiRisk_NoArbitrage
import Definitions.Def_ScalarMultiRisk_piS
import Definitions.Def_ScalarMultiRisk_riskAcceptance
import Definitions.Def_ScalarMultiRisk_IsConditionalCone

open MeasureTheory

namespace ScalarMultiRisk

/-- **Proposition 4.6 (corrected: the last sentence).** arXiv:1807.10694v5, Proposition 4.6, p.20.
For `S ∈ 𝒮` satisfying (NA), `π^S_t` is cash invariant by `S_tᵀ m`, monotone in `S_T^T X`,
conditionally convex and value consistent. If `A_t` is a conditional cone it is positively
homogeneous.

**Formalization Note.** The last sentence as printed fails at `λ = 0` where `π^S_t(0) = −∞`; it
is stated on `{λ > 0} ∪ {π^S_t(0) > −∞}`. `EReal` arithmetic: `−∞ − r = −∞` and `0 · (−∞) = 0`;
items 1 and 3 hold in this arithmetic because `{π^S_t(X) = −∞}` does not depend on `X`. -/
theorem proposition_4_6 {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ)
    (hρ : StandingAssumptions A ρ)
    {S : Fin (T + 1) → Ω → Fin d → ℝ} (hS : S ∈ priceSet A) (hNA : NoArbitrage A.toFilteredSpace S)
    (t : Fin (T + 1)) :
    (∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T), ∀ m ∈ LinftyFull A.toFilteredSpace t,
      piS A ρ S t (X + m) =ᵐ[A.P] fun ω => piS A ρ S t X ω - ((payoff (S t) m ω : ℝ) : EReal)) ∧
    (∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
      ∀ Y ∈ LinftyFull A.toFilteredSpace (Fin.last T),
      (∀ᵐ ω ∂A.P, payoff (S (Fin.last T)) Y ω ≤ payoff (S (Fin.last T)) X ω) →
        piS A ρ S t X ≤ᵐ[A.P] piS A ρ S t Y) ∧
    (∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
      ∀ Y ∈ LinftyFull A.toFilteredSpace (Fin.last T),
      ∀ l ∈ Linfty A.toFilteredSpace t (fun _ => Set.Icc (0 : ℝ) 1),
        piS A ρ S t (fun ω => l ω • X ω + (1 - l ω) • Y ω) ≤ᵐ[A.P]
          fun ω => (l ω : EReal) * piS A ρ S t X ω +
            ((1 - l ω : ℝ) : EReal) * piS A ρ S t Y ω) ∧
    (∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
      piS A ρ S t X =ᵐ[A.P]
        piS A ρ S t fun ω => payoff (S (Fin.last T)) X ω • QKPSDP.e1 d) ∧
    (IsConditionalCone A.toFilteredSpace t (riskAcceptance A ρ t) →
      ∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
      ∀ l ∈ Linfty A.toFilteredSpace t (fun _ => Set.Ici (0 : ℝ)),
        ∀ᵐ ω ∂A.P, (0 < l ω ∨ ⊥ < piS A ρ S t 0 ω) →
          piS A ρ S t (fun ω' => l ω' • X ω') ω = (l ω : EReal) * piS A ρ S t X ω) := by sorry

end ScalarMultiRisk
