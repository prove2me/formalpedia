-- Prove2me | Theorems.Thm_ScalarMultiRisk_proposition_4_7
-- name    : ScalarMultiRisk.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:07.565026+00:00
-- url     : https://prove2.me/theorems/a9f43d89-319f-4455-b9c3-38e867039be6
-- title:
--   Proposition 4.7 — $\pi^S_t(X)\in L^\infty_t(\mathbb R)$ iff $\pi^S_t(0)\in L^\infty_t(\mathbb R)$
-- statement:
--   Let $S\in\mathcal S$ and $X\in L^\infty(\mathbb R^d)$. For any time $t$,
--
--   $$\pi^S_t(X)\in L^\infty_t(\mathbb R)\iff\pi^S_t(0)\in L^\infty_t(\mathbb R).$$
--
--   So boundedness of $\pi^S_t$ can be tested at the zero portfolio alone, which justifies the definition of $\mathcal S_t$.
--
--   Differences from the source:
--   - reading: "for any time $t$" appears on both sides of the equivalence → the equivalence holds separately for each $t$; reason: this is the strongest reading, and it implies the reading with $\forall t$ on each side
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
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proposition 4.7, p.20

import Mathlib
import Definitions.Def_ScalarMultiRisk_StandingAssumptions
import Definitions.Def_ScalarMultiRisk_priceSet
import Definitions.Def_ScalarMultiRisk_piS
import Definitions.Def_ScalarMultiRisk_InLinftyE

open MeasureTheory

namespace ScalarMultiRisk

/-- **Proposition 4.7.** arXiv:1807.10694v5, Proposition 4.7, p.20. For `S ∈ 𝒮`, `X ∈ L∞(ℝ^d)`
and any time `t`: `π^S_t(X) ∈ L∞_t(ℝ)` if and only if `π^S_t(0) ∈ L∞_t(ℝ)`. -/
theorem proposition_4_7 {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ)
    (hρ : StandingAssumptions A ρ)
    {S : Fin (T + 1) → Ω → Fin d → ℝ} (hS : S ∈ priceSet A)
    {X : Ω → Fin d → ℝ} (hX : X ∈ LinftyFull A.toFilteredSpace (Fin.last T))
    (t : Fin (T + 1)) :
    InLinftyE A.toFilteredSpace t (piS A ρ S t X) ↔
      InLinftyE A.toFilteredSpace t (piS A ρ S t 0) := by sorry

end ScalarMultiRisk
