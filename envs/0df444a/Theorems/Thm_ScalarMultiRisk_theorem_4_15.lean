-- Prove2me | Theorems.Thm_ScalarMultiRisk_theorem_4_15
-- name    : ScalarMultiRisk.theorem_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:06.164657+00:00
-- url     : https://prove2.me/theorems/a36fbe6a-5258-468f-bb0e-eaaa5d2adfdf
-- title:
--   Theorem 4.15 (corrected: item 4 for all $\mathbb Q\in\mathcal Q^e(S)$) — time consistency of $\pi^S$ and its equivalent forms
-- statement:
--   Fix $S\in\mathcal S^*$ with $\pi^S_t(0)=0$ for all times $t$. The following are equivalent:
--
--   1. $(\pi^S_t)_{t=0}^T$ is time consistent;
--   2. $\pi^S_t(X)=\pi^S_t(-\pi^S_s(X)e_1)$ for all $t<s$ and $X\in L^\infty(\mathbb R^d)$;
--   3. $A^\pi_t=A^\pi_{t,s}+A^\pi_s$ for all $t<s$;
--   4. $\beta_t(\mathbb Q,S)=\beta^S_{t,s}(\mathbb Q)+\mathbb E^{\mathbb Q}[\beta_s(\mathbb Q,S)\mid\mathcal F_t]$ for all $t<s$ and all $\mathbb Q\in\mathcal Q^e(S)$;
--   5. for all $\mathbb Q\in\mathcal Q^*(S)$ and $X\in L^\infty(\mathbb R^d)$, the process $V^{\mathbb Q}_t(X)=\pi^S_t(X)+\beta_t(\mathbb Q,S)$ is a $\mathbb Q$-supermartingale.
--
--   In each case, for all $X\in L^\infty(\mathbb R^d)$ and all times $t$,
--
--   $$\pi^S_t(X)=\operatorname*{ess\,sup}_{\mathbb Q\in\mathcal Q^*(S)}\Big(-\beta_t(\mathbb Q,S)-\mathbb E^{\mathbb Q}[S_T^{\mathsf T}X\mid\mathcal F_t]\Big).$$
--
--   This is the dynamic programming principle for the frictionless risk measures: it gives the backward recursion, and it is the basis of the paper's notion of $\pi$-time consistency.
--
--   Differences from the source:
--   - correction: item 4 is stated for $\mathbb Q\in\mathcal Q^*(S)$ → item 4 is stated for all $\mathbb Q\in\mathcal Q^e(S)$; reason: the printed item 4 does not imply item 1: with $d=1$, $S\equiv1$, $K_t=[0,\infty)$, $T=2$, four equally likely points, $\mathcal F_1=\{ab\mid cd\}$, $\rho_2(X)=-X$, $\rho_0=-\mathbb E_{\mathbb P}$ and $\rho_1$ the worst case over $\mathbb P(a\mid ab)\in[1/2,3/4]$, $\mathbb P(c\mid cd)=1/2$, one has $\mathcal Q^*(S)=\{\mathbb P\}$ and all penalties of $\mathbb P$ vanish, while $X=1_b$, $Y=(1_a+1_b)/4$ violate time consistency; the cited Föllmer–Penner Theorem 4.5(3) quantifies over all equivalent measures
--   - encoding: hypothesis "normalized and convex" → only $\pi^S_t(0)=0$ a.s. for all $t$; reason: Proposition 4.6(3) proves convexity, so no instance is lost
--   - encoding: Assumption 3.3 assumes a set-valued $R_t$ with $\rho_t$ from (3.1) and $A_t=\{X\mid 0\in R_t(X)\}$ → hypothesis `StandingAssumptions` on $\rho_t$ with $A_t=\{X\mid\rho_t(X)\le0$ a.s.$\}$; reason: Theorem 3.2 gives $R_t(X)=(\rho_t(X)+L^\infty_t(\mathbb R_+))e_1$, so the two formulations have the same instances
--   - encoding: random vectors are a.e.-classes → functions on $\Omega$, with a.e. (in)equalities; reason: same content; every set involved is closed under a.e. modification
--   - reading: time is written $(\mathcal F_t)_{t=0}^T$, with a stray "$[0,T]$" on p.30 → discrete time $t\in\{0,\dots,T\}$; reason: every construction sums over $s=t,\dots,T$
--   - encoding: $\pi^S_t$ takes values in $L^0_t(\mathbb R)\cup\{-\infty\}$ → extended real values; reason: Lean convention; same instances
--   - encoding: $-\pi^S_s(X)e_1$ in item 2 → built from the real part of $\pi^S_s(X)$; reason: $\pi^S_s(X)$ is a.s. finite for $S\in\mathcal S^*$ by Proposition 4.7
--   - encoding: $\mathbb E^{\mathbb Q}[\beta_s(\mathbb Q,S)\mid\mathcal F_t]$ → the conditional Lebesgue expectation of a $[0,\infty]$-valued function; reason: $\beta_s(\mathbb Q,S)\ge-\pi^S_s(0)=0$ and it can be $+\infty$
--   - encoding: "is a $\mathbb Q$-supermartingale" → $\mathbb Q$-a.s. equal to a real supermartingale in the Mathlib sense; reason: the filtration need not contain the null sets; a.s. finiteness is part of the claim
--   - encoding: "in each case" the representation holds → the representation is a consequence of item 1; reason: the five conditions are equivalent, so this is the same claim
--   - reading: “$\mathcal F_s$-measurable random convex cones $K_s$” (p.7), the solvency cones of Assumption 3.3, and the convex cone $\bar K$ → each $K_s(\omega)$ and $\bar K$ is a convex cone containing $0$ (`PointedCone`), and $\{(\omega,x)\mid x\in K_s(\omega)\}$ is $\mathcal F_s\otimes\mathfrak B(\mathbb R^d)$-measurable; no closedness and no $\mathbb R^d_+\subseteq K_s$ is assumed; reason: the paper does not define random cones; graph measurability is the standard notion (Molchanov); solvency cones contain $0$, and the paper uses $0\in\mathbb K_t$ (Theorem 3.2 and after (3.1))
--   - encoding: a filtered probability space satisfying the usual conditions with $\mathcal F_0$ trivial and $\mathcal F=\mathcal F_T$ → $\mathcal F_T$ is the ambient σ-algebra, every $\mathcal F_0$-set has probability $0$ or $1$, and “$\mathcal F_t$-measurable” is a.e. strong measurability for $\mathcal F_t$; reason: in discrete time the usual conditions say that $\mathcal F_0$ contains the null sets, so the $\mathcal F_t$-measurable classes are the same
--   - encoding: asset $i$, $i=1,\dots,d$, with cash $e_1=(1,0,\dots,0)^{\mathsf T}$ → index $i-1$ of `Fin d` with `[NeZero d]`; $e_1$ is the published `QKPSDP.e1 d` (`Pi.single 0 1`); reason: Lean indices start at $0$; same instances
--   - encoding: $\mathbb E^{\mathbb Q}[\cdot\mid\mathcal F_t]$, the $\mathbb P$-a.s. version defined through the density process (p.6) → Mathlib's conditional expectation `Q[·|F t]` under $\mathbb Q$; reason: only $\mathbb Q\sim\mathbb P$ occur, and then the two agree a.s.
--   - encoding: $\|e_i\|_{\mathbb K_T,0}$, an essential infimum over $c\in L^\infty_0(\mathbb R)$ (3.3), and $\mathcal Q^e(S)=\{\mathbb Q\in\mathcal M\mid(\mathbb Q,S)\in\mathcal Q^e_0\}$ → the real infimum over constants $c$ with $ce_1-e_i,\ e_i+ce_1\in K_T$ a.s.; `Qe` lists only the conditions of $\mathcal Q_0$ not already in (4.3); reason: $\mathcal F_0$ is trivial and the set of such $c$ is nonempty and contained in $[0,\infty)$ under the standing assumptions; every statement takes $S\in\mathcal S$
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Theorem 4.15, pp.24–25

import Mathlib
import Definitions.Def_ScalarMultiRisk_StandingAssumptions
import Definitions.Def_ScalarMultiRisk_priceSetStar
import Definitions.Def_ScalarMultiRisk_TimeConsistent
import Definitions.Def_ScalarMultiRisk_ApiStep
import Definitions.Def_ScalarMultiRisk_betaStep
import Definitions.Def_ScalarMultiRisk_QStar
import Definitions.Def_ScalarMultiRisk_condExpNonneg
import Definitions.Def_ScalarMultiRisk_IsSupermartingaleE

open MeasureTheory Pointwise

namespace ScalarMultiRisk

/-- **Theorem 4.15 (corrected: item 4 for all `ℚ ∈ 𝒬^e(S)`).** arXiv:1807.10694v5, Theorem 4.15,
pp.24–25. Fix `S ∈ 𝒮*` with
`π^S_t(0) = 0` for all times. The following are equivalent:
(1) `(π^S_t)` is time consistent;
(2) `π^S_t(X) = π^S_t(−π^S_s(X)e₁)` for all `t < s` and `X ∈ L∞(ℝ^d)`;
(3) `A^π_t = A^π_{t,s} + A^π_s` for all `t < s`;
(4) `β_t(ℚ,S) = β^S_{t,s}(ℚ) + 𝔼^ℚ[β_s(ℚ,S) | F_t]` for all `t < s` and `ℚ ∈ 𝒬^e(S)`;
(5) for all `ℚ ∈ Q*(S)` and `X ∈ L∞(ℝ^d)`, `V^ℚ_t(X) := π^S_t(X) + β_t(ℚ,S)` is a
`ℚ`-supermartingale.
In each case `π^S_t(X) = ess sup_{ℚ ∈ Q*(S)} (−β_t(ℚ,S) − 𝔼^ℚ[S_T^T X | F_t])` for all `X` and
all times `t`.

**Formalization Note.** "Convex" is not a hypothesis: Proposition 4.6(3) proves it. In (2),
`π^S_s(X)` is a.s. finite for `S ∈ 𝒮*` (Prop 4.7), so it is formed from its real part. In (4) all
terms are `≥ 0`, so the `EReal` sum has no `⊥ + ⊤`. Since the five conditions are equivalent,
the representation is stated as a consequence of (1).

The paper prints (4) for `ℚ ∈ Q*(S)` only. That version does not imply (1): take `d = 1`, `S ≡ 1`,
`K_t = [0, ∞)`, `T = 2`, four equally likely points, `F₁ = {ab | cd}`, `ρ₂(X) = −X`,
`ρ₀ = −𝔼_ℙ`, and `ρ₁` the worst case over `ℙ(a | ab) ∈ [1/2, 3/4]`, `ℙ(c | cd) = 1/2`. Then
`Q*(S) = {ℙ}`, all penalties of `ℙ` vanish, so the printed (4) holds, but `X = 1_b` and
`Y = (1_a + 1_b)/4` have `ρ₁(X) = ρ₁(Y)` and `ρ₀(X) < ρ₀(Y)`. The theorem the paper cites,
Föllmer–Penner Theorem 4.5(3), quantifies over all equivalent measures; here that is `𝒬^e(S)`. -/
theorem theorem_4_15 {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ)
    (hρ : StandingAssumptions A ρ)
    {S : Fin (T + 1) → Ω → Fin d → ℝ} (hS : S ∈ priceSetStar A ρ)
    (hnorm : ∀ t, piS A ρ S t 0 =ᵐ[A.P] 0) :
    List.TFAE [
      TimeConsistent A.toFilteredSpace (fun t => piS A ρ S t),
      ∀ t s : Fin (T + 1), t < s → ∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
        piS A ρ S t X =ᵐ[A.P]
          piS A ρ S t fun ω => (-(piS A ρ S s X ω).toReal) • QKPSDP.e1 d,
      ∀ t s : Fin (T + 1), t < s → Api A ρ S t = ApiStep A ρ S t s + Api A ρ S s,
      ∀ t s : Fin (T + 1), t < s → ∀ Q ∈ Qe A S,
        beta A ρ t Q S =ᵐ[A.P] fun ω =>
          betaStep A ρ S t s Q ω + condExpNonneg A.toFilteredSpace Q t (beta A ρ s Q S) ω,
      ∀ Q ∈ QStar A ρ S, ∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
        IsSupermartingaleE A.toFilteredSpace Q
          fun t ω => piS A ρ S t X ω + beta A ρ t Q S ω] ∧
    (TimeConsistent A.toFilteredSpace (fun t => piS A ρ S t) →
      ∀ t, ∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
        CondConvexRisk.Representation.IsEssSup A.P
          (fun Q : QStar A ρ S => dualTerm A ρ S t Q.1 (payoff (S (Fin.last T)) X))
          (piS A ρ S t X)) := by sorry

end ScalarMultiRisk
