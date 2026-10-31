-- Prove2me | Theorems.Thm_ScalarMultiRisk_proposition_4_9
-- name    : ScalarMultiRisk.proposition_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:47.861091+00:00
-- url     : https://prove2.me/theorems/b0567ec9-3834-4845-a524-3f41c29672e9
-- title:
--   Proposition 4.9 — $\phi^S_t$ is a univariate convex risk measure and $\pi^S_t(X)=\phi^S_t(S_T^{\mathsf T}X)$
-- statement:
--   Let $S\in\mathcal S_t$. The map $\phi^S_t(Z)=\pi^S_t(Ze_1)$ takes a.s. real values on $L^\infty(\mathbb R)$ and is a scalarized conditional convex risk measure on $L^\infty(\mathbb R)$ (Definition 3.1 with $d=1$). It is coherent if $A_t$ is a conditional cone. Moreover,
--
--   $$\pi^S_t(X)=\phi^S_t(S_T^{\mathsf T}X)\quad\text{for every }X\in L^\infty(\mathbb R^d).$$
--
--   This is the reduction of the frictionless multivariate problem to the univariate theory of dynamic risk measures.
--
--   Differences from the source:
--   - reading: "a convex (coherent) univariate scalar risk measure" → Definition 3.1 with $d=1$, and conditionally positively homogeneous when $A_t$ is a conditional cone; reason: the paper defines neither term; its proof checks exactly these properties
--   - encoding: Assumption 3.3 assumes a set-valued $R_t$ with $\rho_t$ from (3.1) and $A_t=\{X\mid 0\in R_t(X)\}$ → hypothesis `StandingAssumptions` on $\rho_t$ with $A_t=\{X\mid\rho_t(X)\le0$ a.s.$\}$; reason: Theorem 3.2 gives $R_t(X)=(\rho_t(X)+L^\infty_t(\mathbb R_+))e_1$, so the two formulations have the same instances
--   - encoding: random vectors are a.e.-classes → functions on $\Omega$, with a.e. (in)equalities; reason: same content; every set involved is closed under a.e. modification
--   - reading: time is written $(\mathcal F_t)_{t=0}^T$, with a stray "$[0,T]$" on p.30 → discrete time $t\in\{0,\dots,T\}$; reason: every construction sums over $s=t,\dots,T$
--   - encoding: $\phi^S_t:L^\infty(\mathbb R)\to L^\infty_t(\mathbb R)$ → the risk measure properties are stated for the real part `phiReal`, together with the a.s. equality of $\phi^S_t$ and its real part; reason: same content, since the values are a.s. finite
--   - reading: “$\mathcal F_s$-measurable random convex cones $K_s$” (p.7), the solvency cones of Assumption 3.3, and the convex cone $\bar K$ → each $K_s(\omega)$ and $\bar K$ is a convex cone containing $0$ (`PointedCone`), and $\{(\omega,x)\mid x\in K_s(\omega)\}$ is $\mathcal F_s\otimes\mathfrak B(\mathbb R^d)$-measurable; no closedness and no $\mathbb R^d_+\subseteq K_s$ is assumed; reason: the paper does not define random cones; graph measurability is the standard notion (Molchanov); solvency cones contain $0$, and the paper uses $0\in\mathbb K_t$ (Theorem 3.2 and after (3.1))
--   - encoding: a filtered probability space satisfying the usual conditions with $\mathcal F_0$ trivial and $\mathcal F=\mathcal F_T$ → $\mathcal F_T$ is the ambient σ-algebra, every $\mathcal F_0$-set has probability $0$ or $1$, and “$\mathcal F_t$-measurable” is a.e. strong measurability for $\mathcal F_t$; reason: in discrete time the usual conditions say that $\mathcal F_0$ contains the null sets, so the $\mathcal F_t$-measurable classes are the same
--   - encoding: asset $i$, $i=1,\dots,d$, with cash $e_1=(1,0,\dots,0)^{\mathsf T}$ → index $i-1$ of `Fin d` with `[NeZero d]`; $e_1$ is the published `QKPSDP.e1 d` (`Pi.single 0 1`); reason: Lean indices start at $0$; same instances
--   - encoding: $\mathbb E^{\mathbb Q}[\cdot\mid\mathcal F_t]$, the $\mathbb P$-a.s. version defined through the density process (p.6) → Mathlib's conditional expectation `Q[·|F t]` under $\mathbb Q$; reason: only $\mathbb Q\sim\mathbb P$ occur, and then the two agree a.s.
--   - encoding: $\|e_i\|_{\mathbb K_T,0}$, an essential infimum over $c\in L^\infty_0(\mathbb R)$ (3.3), and $\mathcal Q^e(S)=\{\mathbb Q\in\mathcal M\mid(\mathbb Q,S)\in\mathcal Q^e_0\}$ → the real infimum over constants $c$ with $ce_1-e_i,\ e_i+ce_1\in K_T$ a.s.; `Qe` lists only the conditions of $\mathcal Q_0$ not already in (4.3); reason: $\mathcal F_0$ is trivial and the set of such $c$ is nonempty and contained in $[0,\infty)$ under the standing assumptions; every statement takes $S\in\mathcal S$
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proposition 4.9, p.22

import Mathlib
import Definitions.Def_ScalarMultiRisk_StandingAssumptions
import Definitions.Def_ScalarMultiRisk_priceSetAt
import Definitions.Def_ScalarMultiRisk_phiReal
import Definitions.Def_ScalarMultiRisk_IsScalarRisk
import Definitions.Def_ScalarMultiRisk_IsCoherent
import Definitions.Def_ScalarMultiRisk_riskAcceptance
import Definitions.Def_ScalarMultiRisk_IsConditionalCone
import Definitions.Def_ScalarMultiRisk_payoff

open MeasureTheory

namespace ScalarMultiRisk

/-- **Proposition 4.9.** arXiv:1807.10694v5, Proposition 4.9, p.22. For `S ∈ 𝒮_t`, the map
`φ^S_t(Z) := π^S_t(Z e₁)` is real valued a.s. and a convex univariate scalar risk measure, coherent
if `A_t` is a conditional cone, and `π^S_t(X) = φ^S_t(S_T^T X)` for any `X ∈ L∞(ℝ^d)`. -/
theorem proposition_4_9 {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ)
    (hρ : StandingAssumptions A ρ)
    {t : Fin (T + 1)} {S : Fin (T + 1) → Ω → Fin d → ℝ} (hS : S ∈ priceSetAt A ρ t) :
    (∀ Z ∈ (LinftyFull A.toFilteredSpace (Fin.last T) : Set (Ω → ℝ)),
      phiS A ρ S t Z =ᵐ[A.P] fun ω => (phiReal A ρ S t Z ω : EReal)) ∧
    IsScalarRisk A.toFilteredSpace t (1 : ℝ) (phiReal A ρ S t) ∧
    (IsConditionalCone A.toFilteredSpace t (riskAcceptance A ρ t) →
      IsCoherent A.toFilteredSpace t (phiReal A ρ S t)) ∧
    (∀ X ∈ LinftyFull A.toFilteredSpace (Fin.last T),
      piS A ρ S t X =ᵐ[A.P] phiS A ρ S t (payoff (S (Fin.last T)) X)) := by sorry

end ScalarMultiRisk
