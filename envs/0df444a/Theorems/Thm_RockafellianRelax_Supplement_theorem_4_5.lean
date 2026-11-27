-- Prove2me | Theorems.Thm_RockafellianRelax_Supplement_theorem_4_5
-- name    : RockafellianRelax.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:18:14.947722+00:00
-- url     : https://prove2.me/theorems/ca3d1694-f227-50c3-bc44-d908fe760038
-- title:
--   Theorem 4.5 — exactness under probability and support uncertainty (corrected: strictness needs $\operatorname{dom}\varphi\ne\emptyset$)
-- statement:
--   Let $f_0:\mathbb R^n\to\overline{\mathbb R}$ and $g:\mathbb R^m\times\mathbb R^n\to\overline{\mathbb R}$ be proper and lower semicontinuous ($g$ jointly), let $p\in\Delta$ (the probability simplex in $\mathbb R^s$) and $\xi=(\xi_1,\dots,\xi_s)\in\mathbb R^{sm}$, and let $\varphi(x)=f_0(x)+\sum_{i=1}^s p_i g(\xi_i,x)$ be the objective of (4.8). For $(u,v)\in\mathbb R^{s+sm}$ let $f((u,v),x)$ be $\varphi(x)$ at $(u,v)=0$ and $+\infty$ otherwise, as in (4.9). Then:
--
--   1. $f$ is an exact Rockafellian for $\varphi$, supported by every $\bar y\in\mathbb R^{s+sm}$;
--   2. if $\operatorname{dom}\varphi\ne\emptyset$, then $f$ is strictly exact, supported by every $\bar y\in\mathbb R^{s+sm}$;
--   3. for all $p^\nu\in\Delta$, $\xi^\nu\in\mathbb R^{sm}$ and $\theta^\nu,\lambda^\nu\ge0$ with $\theta^\nu,\lambda^\nu\to\infty$, $\theta^\nu\|p^\nu-p\|_2^2\to0$ and $\lambda^\nu\|\xi^\nu-\xi\|_2^2\to0$, the functions
--   $$
--   f^\nu((u,v),x)=f_0(x)+\sum_{i=1}^s(p^\nu_i+u_i)g(\xi^\nu_i+v_i,x)+\tfrac12\theta^\nu\|u\|_2^2+\tfrac12\lambda^\nu\|v\|_2^2
--   $$
--   for $p^\nu+u\in\Delta$, and $+\infty$ otherwise, as in (4.10), epi-converge to $f$; if also $\operatorname{dom}\varphi\ne\emptyset$, they are strictly limit-exact Rockafellians for $\varphi$, supported by every $\bar y$.
--
--   The premise $\operatorname{dom}\varphi\ne\emptyset$ in the strict claims corrects the printed theorem. Exactness and epi-convergence do not need it.
--
--   The theorem extends the relaxation to changes in the support as well as in the probabilities of the distribution.
--
--   **Formalization Note** The pair $(u,v)$ is one vector in $\mathbb R^{s+sm}$. Items 1 and 2 use no hypothesis on sequences. The sections $g(\xi_i,\cdot)$ need not be proper.
--
--   Differences from the source:
--
--   - correction: f is strictly exact, and f^ν strictly limit-exact, for all proper lsc f₀ and g → exactness and epi-convergence with no added premise; both strict claims when dom φ ≠ ∅; reason: if φ ≡ ∞ then the strict inequality of Definition 3.1 is ∞ > ∞, false: n = m = s = 1, p = p^ν = 1, ξ = ξ^ν = 0, f₀ the indicator of {0}, g(ξ, x) the indicator of x = 1, θ^ν = λ^ν = ν; the only excluded case of the strict clauses is φ ≡ ∞
--   - reading: strictly limit-exact Rockafellians, with no support named in the second sentence → supported by every ȳ ∈ ℝ^{s+sm}; reason: the first sentence gives every ȳ as a support of the same f; this is the stronger reading
--   - encoding: strictly limit-exact Rockafellians with f as their limit → epi-convergence to this f and strict exactness of this f, stated next to IsStrictlyLimitExact; reason: the published predicate quantifies the limit existentially, while the paper names it
--   - encoding: (u, v) ∈ ℝ^{s+sm}, ξ ∈ ℝ^{sm} → u and v are the split of Fin (s + s * m) → ℝ, and ξ is Fin s → Fin m → ℝ with the sum of all squared coordinates; reason: coordinate bijections, the same instances
--   - encoding: sums containing indicator functions, under ∞ − ∞ = ∞ → definitions by cases: the formula on the feasible set, +∞ elsewhere; reason: EReal has −∞ + ∞ = −∞, and the cases give exactly the paper's values
--   - encoding: ℝⁿ, R̄, i = 1, …, s, ν ∈ ℕ = {1, 2, …}, sequential lower semicontinuity → Fin n → ℝ, EReal, Fin s, ν from 0, LowerSemicontinuous; reason: Lean conventions with the same instances; the two notions of lower semicontinuity agree on ℝⁿ
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 4.5, p.17, with displays (4.8)–(4.10), p.16

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
import Definitions.Def_RockafellianRelax_Supplement_supportApprox
open Filter Topology

namespace RockafellianRelax.Supplement

/-- **Theorem 4.5 (exactness in expectation minimization; support uncertainty), corrected at
`φ ≡ ∞`.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, Theorem 4.5, p.17: "Suppose that f₀ : ℝⁿ → R̄ and g : ℝᵐ × ℝⁿ → R̄ are proper lsc
functions and p, pν ∈ ∆. For the actual problem (4.8), the Rockafellian f in (4.9) is strictly
exact, supported by any ȳ ∈ ℝ^{s+sm}. If θν, λν → ∞, θν‖pν − p‖₂² → 0, and λν‖ξν − ξ‖₂² → 0,
where ξ = (ξ₁, …, ξ_s) ∈ ℝ^{sm}, then the functions {fν, ν ∈ ℕ} in (4.10) are strictly limit-exact
Rockafellians with f as their limit."

Conjuncts: (1) `f` is exact, supported by every `ȳ`; (2) if `dom φ ≠ ∅`, it is strictly exact,
supported by every `ȳ`; (3) under the sequence hypotheses, `fν` epi-converge to `f` and, if
`dom φ ≠ ∅`, are strictly limit-exact, supported by every `ȳ`. The premise `dom φ ≠ ∅` is the
correction: for `φ ≡ ∞` the strict inequality of Definition 3.1 is `∞ > ∞`.

**Formalization Note.** `(u, v) ∈ ℝ^{s+sm}` is one vector `Fin (s + s * m) → ℝ`, and (4.9) is
`trivialRockafellian φ`. (1) and (2) use no sequence hypothesis. `g` is lsc jointly; its sections
need not be proper, continuous or finite. `‖ξν − ξ‖₂²` sums over all `sm` coordinates. -/
theorem theorem_4_5 {m n s : ℕ} (f0 : (Fin n → ℝ) → EReal)
    (g : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (p : Fin s → ℝ) (hp : p ∈ stdSimplex ℝ (Fin s))
    (hf0 : IsProper f0) (hf0lsc : LowerSemicontinuous f0)
    (hg : IsProper g) (hglsc : LowerSemicontinuous g) (ξ : Fin s → Fin m → ℝ) :
    let φ : (Fin n → ℝ) → EReal := expObjective f0 (fun i x => g (ξ i, x)) p
    let f : (Fin (s + s * m) → ℝ) × (Fin n → ℝ) → EReal := trivialRockafellian φ
    (∀ ybar : Fin (s + s * m) → ℝ, IsExact f φ ybar) ∧
      ((AubinLipschitz.effDom φ).Nonempty →
        ∀ ybar : Fin (s + s * m) → ℝ, IsStrictlyExact f φ ybar) ∧
      ∀ (pseq : ℕ → Fin s → ℝ) (ξseq : ℕ → Fin s → Fin m → ℝ) (θ lam : ℕ → ℝ),
        (∀ ν, pseq ν ∈ stdSimplex ℝ (Fin s)) → (∀ ν, 0 ≤ θ ν) → (∀ ν, 0 ≤ lam ν) →
        Tendsto θ atTop atTop → Tendsto lam atTop atTop →
        Tendsto (fun ν => θ ν * euclidNorm (pseq ν - p) ^ 2) atTop (𝓝 0) →
        Tendsto (fun ν => lam ν * ∑ i, ∑ j, (ξseq ν i j - ξ i j) ^ 2) atTop (𝓝 0) →
        let F : ℕ → (Fin (s + s * m) → ℝ) × (Fin n → ℝ) → EReal :=
          fun ν => supportApprox f0 g (pseq ν) (ξseq ν) (θ ν) (lam ν)
        PerspEpi.SeqEpiConv F f ∧
          ((AubinLipschitz.effDom φ).Nonempty →
            ∀ ybar : Fin (s + s * m) → ℝ, IsStrictlyLimitExact F φ ybar) := by sorry

end RockafellianRelax.Supplement
