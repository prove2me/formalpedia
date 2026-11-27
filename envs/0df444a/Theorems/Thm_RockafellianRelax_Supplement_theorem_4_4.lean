-- Prove2me | Theorems.Thm_RockafellianRelax_Supplement_theorem_4_4
-- name    : RockafellianRelax.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:17:40.553367+00:00
-- url     : https://prove2.me/theorems/41cb8b76-97f6-56ab-ab20-66d051983510
-- title:
--   Theorem 4.4 — $\Phi$-divergence approximations are strictly limit-exact (corrected: strictness needs $\operatorname{dom}\varphi\ne\emptyset$)
-- statement:
--   Let $f_i : \mathbb R^n\to\overline{\mathbb R}$, $i = 0,1,\dots,s$, be proper and lower semicontinuous, let $p \in \Delta = \{q\in[0,\infty)^s \mid \sum_i q_i = 1\}$, and let $\varphi = f_0 + \sum_{i=1}^s p_i f_i$ be the objective of the actual problem (2.1), with $0\cdot\infty = 0$. Let $\Phi:\mathbb R\to\overline{\mathbb R}$ be convex, real-valued on $[0,\infty)$, with $\Phi(1)=0<\Phi(a)$ for $a\ne1$, and let $d_\Phi$ be its divergence, with the conventions $0\cdot\Phi(0/0)=0$ and $0\cdot\Phi(\beta/0)=\beta\lim_{\alpha\to\infty}\Phi(\alpha)/\alpha$ for $\beta>0$. Let $p^\nu\in\Delta$ and $\theta^\nu\ge0$ satisfy $\theta^\nu\to\infty$ and $\theta^\nu\|p^\nu-p\|_2\to0$. Let $f(u,x)$ be $\varphi(x)$ at $u=0$ and $+\infty$ otherwise, as in (4.2), and let
--
--   $$
--   f^\nu(u,x)=f_0(x)+\sum_{i=1}^s(p^\nu_i+u_i)f_i(x)+\theta^\nu d_\Phi(p^\nu+u\,|\,p^\nu)
--   $$
--
--   if $p^\nu+u\in\Delta$ and $+\infty$ otherwise, as in (4.7). Then:
--
--   1. $f^\nu$ epi-converges to $f$;
--   2. $f$ is an exact Rockafellian for $\varphi$, supported by every $\bar y\in\mathbb R^s$;
--   3. if $\operatorname{dom}\varphi\ne\emptyset$, then for every $\bar y\in\mathbb R^s$ the function $f$ is strictly exact and $\{f^\nu\}$ are strictly limit-exact Rockafellians for $\varphi$, supported by $\bar y$.
--
--   The premise in item 3 corrects the printed theorem, which claims strictness also for an infeasible actual problem. Items 1 and 2 do not need it.
--
--   The theorem justifies Theorem 3.7's convergence conclusion for divergence-penalized relaxations.
--
--   **Formalization Note** The rate is not squared. The limit $f$ is named in every item.
--
--   Differences from the source:
--
--   - correction: f^ν are strictly limit-exact with f as their limit, for all proper lsc f_i → epi-convergence and exactness with no added premise; strict exactness and strict limit-exactness when dom φ ≠ ∅; reason: if φ ≡ ∞ then 𝒱 ≡ ∞ and the strict inequality of Definition 3.1 is ∞ > ∞, false: n = s = 1, p = p^ν = 1, f₀ the indicator of {0}, f₁ the indicator of {1}, Φ(α) = (α − 1)², θ^ν = ν; the only excluded case of the strict clause is φ ≡ ∞
--   - reading: strictly limit-exact Rockafellians, with no support named → supported by every ȳ ∈ ℝˢ; reason: Proposition 4.1 (p.10) gives every ȳ as a support of the same f from (4.2); this is the stronger reading
--   - encoding: strictly limit-exact Rockafellians with f as their limit → epi-convergence to this f and strict exactness of this f, stated next to IsStrictlyLimitExact; reason: the published predicate quantifies the limit existentially, while the paper names it
--   - encoding: lim_{α→∞} Φ(α)/α in the convention for 0 · Φ(β/0) → limsup in EReal; reason: the limit exists for convex Φ, and then equals the limsup
--   - encoding: sums containing indicator functions, under ∞ − ∞ = ∞ → definitions by cases: the formula on the feasible set, +∞ elsewhere; reason: EReal has −∞ + ∞ = −∞, and the cases give exactly the paper's values
--   - encoding: ℝⁿ, R̄, i = 1, …, s, ν ∈ ℕ = {1, 2, …}, sequential lower semicontinuity → Fin n → ℝ, EReal, Fin s, ν from 0, LowerSemicontinuous; reason: Lean conventions with the same instances; the two notions of lower semicontinuity agree on ℝⁿ
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 4.4, p.15, with displays (4.2), p.10 and (4.7), p.15

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_SeqEpiConv
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_RockafellianRelax_IsStrictlyLimitExact
import Definitions.Def_RockafellianRelax_Supplement_IsProper
import Definitions.Def_RockafellianRelax_Supplement_euclidNorm
import Definitions.Def_RockafellianRelax_Supplement_expObjective
import Definitions.Def_RockafellianRelax_Supplement_trivialRockafellian
import Definitions.Def_RockafellianRelax_Supplement_IsDivergenceFn
import Definitions.Def_RockafellianRelax_Supplement_phiApprox
open Filter Topology

namespace RockafellianRelax.Supplement

/-- **Theorem 4.4 (exactness in expectation minimization; Φ-divergence), corrected at `φ ≡ ∞`.**
Royset, Chen & Eckstrand, arXiv:2204.04762v4, Theorem 4.4, p.15: "In the setting of Subsection 4.1 with p, pν ∈ ∆ and proper lsc
f_i : ℝⁿ → R̄, i = 0, 1, …, s, consider f from (4.2) and fν from (4.7). The functions {fν, ν ∈ ℕ}
are strictly limit-exact Rockafellians with f as their limit provided that θν → ∞ and
θν‖pν − p‖₂ → 0."

Conjuncts: (1) `fν` epi-converge to `f`; (2) `f` is exact, supported by every `ȳ`; (3) if
`dom φ ≠ ∅`, then `f` is strictly exact and the `fν` are strictly limit-exact, supported by every
`ȳ`. The premise in (3) is the correction: for `φ ≡ ∞`, which proper lsc data allow, `𝒱 ≡ ∞` and
the strict inequality of Definition 3.1 fails.

**Formalization Note.** (4.2) is `trivialRockafellian φ` with `φ = expObjective f0 fi p`. The limit
`f` is named in every conjunct, since `IsStrictlyLimitExact` by itself hides it. The rate is not
squared. "Any `ȳ`" is the support that Proposition 4.1 (p.10) gives for (4.2). -/
theorem theorem_4_4 {n s : ℕ} (f0 : (Fin n → ℝ) → EReal) (fi : Fin s → (Fin n → ℝ) → EReal)
    (p : Fin s → ℝ) (hp : p ∈ stdSimplex ℝ (Fin s))
    (hf0 : IsProper f0) (hf0lsc : LowerSemicontinuous f0)
    (hfi : ∀ i, IsProper (fi i)) (hfilsc : ∀ i, LowerSemicontinuous (fi i))
    (Φ : ℝ → EReal) (hΦ : IsDivergenceFn Φ)
    (pseq : ℕ → Fin s → ℝ) (hpseq : ∀ ν, pseq ν ∈ stdSimplex ℝ (Fin s))
    (θ : ℕ → ℝ) (hθ0 : ∀ ν, 0 ≤ θ ν) (hθ : Tendsto θ atTop atTop)
    (hrate : Tendsto (fun ν => θ ν * euclidNorm (pseq ν - p)) atTop (𝓝 0)) :
    let φ : (Fin n → ℝ) → EReal := expObjective f0 fi p
    let f : (Fin s → ℝ) × (Fin n → ℝ) → EReal := trivialRockafellian φ
    let F : ℕ → (Fin s → ℝ) × (Fin n → ℝ) → EReal := fun ν => phiApprox f0 fi Φ (pseq ν) (θ ν)
    PerspEpi.SeqEpiConv F f ∧
      (∀ ybar : Fin s → ℝ, IsExact f φ ybar) ∧
      ((AubinLipschitz.effDom φ).Nonempty →
        ∀ ybar : Fin s → ℝ, IsStrictlyExact f φ ybar ∧ IsStrictlyLimitExact F φ ybar) := by sorry

end RockafellianRelax.Supplement
