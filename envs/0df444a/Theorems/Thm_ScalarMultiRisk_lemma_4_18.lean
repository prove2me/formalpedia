-- Prove2me | Theorems.Thm_ScalarMultiRisk_lemma_4_18
-- name    : ScalarMultiRisk.lemma_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:46.545598+00:00
-- url     : https://prove2.me/theorems/a99d34f3-240e-4e00-a813-7a97844dadea
-- title:
--   Lemma 4.18 — acceptance-set sums for $\pi^S$ and $\phi^S$
-- statement:
--   Let $S\in\mathcal S^*$ and $0\le t\le s\le T$.
--
--   1. Let $D\subseteq L^\infty_s(\mathbb R^d)$ satisfy $D+\Gamma_s(S_s)\subseteq D$. Then for $X\in L^\infty(\mathbb R^d)$,
--
--   $$X\in D+A^\pi_s\iff-\pi^S_s(X)\in S_s^{\mathsf T}D.$$
--
--   2. $A^\phi_{t,s}+A^\phi_s=S_T^{\mathsf T}\big[A^\pi_{t,s}+A^\pi_s\big]$.
--
--   This relates the acceptance-set form of time consistency for $\pi^S$ to the one for $\phi^S$.
--
--   Differences from the source:
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
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Lemma 4.18, pp.25–26

import Mathlib
import Definitions.Def_ScalarMultiRisk_StandingAssumptions
import Definitions.Def_ScalarMultiRisk_priceSetStar
import Definitions.Def_ScalarMultiRisk_ApiStep
import Definitions.Def_ScalarMultiRisk_AphiStep
import Definitions.Def_ScalarMultiRisk_Gamma
import Definitions.Def_ScalarMultiRisk_payoffImage

open MeasureTheory Pointwise

namespace ScalarMultiRisk

/-- **Lemma 4.18.** arXiv:1807.10694v5, Lemma 4.18, pp.25–26. For `S ∈ 𝒮*` and `0 ≤ t ≤ s ≤ T`:
(1) if `D ⊆ L∞_s(ℝ^d)` and `D + Γ_s(S_s) ⊆ D`, then `X ∈ D + A^π_s` if and only if
`−π^S_s(X) ∈ S_s^T D`;
(2) `A^φ_{t,s} + A^φ_s = S_T^T [A^π_{t,s} + A^π_s]`.

**Formalization Note.** The sums are pointwise sums of the function sets. All the sets are closed
under a.e. modification, so this is the Minkowski sum of the classes. -/
theorem lemma_4_18 {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ)
    (hρ : StandingAssumptions A ρ)
    {S : Fin (T + 1) → Ω → Fin d → ℝ} (hS : S ∈ priceSetStar A ρ)
    {t s : Fin (T + 1)} (hts : t ≤ s) :
    (∀ D : Set (Ω → Fin d → ℝ), D ⊆ LinftyFull A.toFilteredSpace s →
      D + Gamma A.toFilteredSpace S s ⊆ D →
      ∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
        (X ∈ D + Api A ρ S s ↔
          ∃ Y ∈ D, (fun ω => ((payoff (S s) Y ω : ℝ) : EReal)) =ᵐ[A.P]
            fun ω => -piS A ρ S s X ω)) ∧
    AphiStep A ρ S t s + Aphi A ρ S s =
      payoffImage A.P (S (Fin.last T)) (ApiStep A ρ S t s + Api A ρ S s) := by sorry

end ScalarMultiRisk
