-- Prove2me | Theorems.Thm_ScalarMultiRisk_corollary_4_11
-- name    : ScalarMultiRisk.corollary_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:21.377017+00:00
-- url     : https://prove2.me/theorems/8145c3fb-5d95-4245-87ab-b8f4cb3b00bc
-- title:
--   Corollary 4.11 — acceptance set and penalty of the stepped risk measure $\phi^S_{t,s}$
-- statement:
--   Let $S\in\mathcal S_t$ and $t<s$, and let $\phi^S_{t,s}$ be the restriction of $\phi^S_t$ to $L^\infty_s(\mathbb R)$. Then:
--
--   1. $A^\phi_{t,s}=S_s^{\mathsf T}A^\pi_{t,s}$, where $A^\pi_{t,s}=A^\pi_t\cap L^\infty_s(\mathbb R^d)$, and consequently $\phi^S_{t,s}(Z)=\operatorname{ess\,inf}\{m\in L^\infty_t(\mathbb R)\mid Z+m\in S_s^{\mathsf T}A^\pi_{t,s}\}$ for $Z\in L^\infty_s(\mathbb R)$;
--   2. for every $\mathbb Q\in\mathcal Q^e(S)$, the minimal penalty of $\phi^S_{t,s}$ is
--
--   $$\operatorname*{ess\,sup}_{Z\in A^\phi_{t,s}}-\mathbb E^{\mathbb Q}[Z\mid\mathcal F_t]=\operatorname*{ess\,sup}_{X\in A^\pi_{t,s}}-\mathbb E^{\mathbb Q}[S_s^{\mathsf T}X\mid\mathcal F_t]=\beta^S_{t,s}(\mathbb Q).$$
--
--   The stepped objects enter the penalty decomposition of Theorem 4.15.
--
--   Differences from the source:
--   - reading: "primal and dual representations are defined via the acceptance set and penalty function … given in" items 1 and 2 → three claims: the acceptance set identity, the primal representation of $\phi^S_{t,s}$, and the identity of the minimal penalty with the formula of item 2; reason: Remark 4.12 says a dual representation of $\phi^S_{t,s}$ over $\mathcal Q^e(S)$ can fail, so none is read in
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
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Corollary 4.11, p.23

import Mathlib
import Definitions.Def_ScalarMultiRisk_StandingAssumptions
import Definitions.Def_ScalarMultiRisk_priceSetAt
import Definitions.Def_ScalarMultiRisk_phiS
import Definitions.Def_ScalarMultiRisk_ApiStep
import Definitions.Def_ScalarMultiRisk_AphiStep
import Definitions.Def_ScalarMultiRisk_betaStep
import Definitions.Def_ScalarMultiRisk_payoffImage
import Definitions.Def_ScalarMultiRisk_IsEssInf

open MeasureTheory

namespace ScalarMultiRisk

/-- **Corollary 4.11.** arXiv:1807.10694v5, Corollary 4.11, p.23. For `S ∈ 𝒮_t` and `t < s`, the
restriction `φ^S_{t,s}` of `φ^S_t` to `L∞_s(ℝ)` has
(1) acceptance set `A^φ_{t,s} = S_s^T A^π_{t,s}`, and so the primal representation
`φ^S_{t,s}(Z) = ess inf{m ∈ L∞_t(ℝ) | Z + m ∈ S_s^T A^π_{t,s}}`;
(2) minimal penalty `ess sup_{Z ∈ A^φ_{t,s}} −𝔼^ℚ[Z | F_t] = β^S_{t,s}(ℚ)` for any
`ℚ ∈ 𝒬^e(S)`. -/
theorem corollary_4_11 {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ)
    (hρ : StandingAssumptions A ρ)
    {t s : Fin (T + 1)} (hts : t < s)
    {S : Fin (T + 1) → Ω → Fin d → ℝ} (hS : S ∈ priceSetAt A ρ t) :
    AphiStep A ρ S t s = payoffImage A.P (S s) (ApiStep A ρ S t s) ∧
    (∀ Z ∈ (LinftyFull A.toFilteredSpace s : Set (Ω → ℝ)),
      IsEssInf A.P
        (fun m : {m : Ω → ℝ // m ∈ LinftyFull A.toFilteredSpace t ∧
            Z + m ∈ payoffImage A.P (S s) (ApiStep A ρ S t s)} =>
          fun ω => (m.1 ω : EReal))
        (phiS A ρ S t Z)) ∧
    (∀ Q ∈ Qe A S,
      CondConvexRisk.Representation.IsEssSup A.P
        (fun Z : AphiStep A ρ S t s => fun ω => ((-(Q[Z.1 | A.F t] ω) : ℝ) : EReal))
        (betaStep A ρ S t s Q)) := by sorry

end ScalarMultiRisk
