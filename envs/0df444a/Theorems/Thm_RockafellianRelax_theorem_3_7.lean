-- Prove2me | Theorems.Thm_RockafellianRelax_theorem_3_7
-- name    : RockafellianRelax.theorem_3_7
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:37:55.116967+00:00
-- url     : https://prove2.me/theorems/c8f795de-5555-498a-92eb-759d75e28bd1
-- title:
--   Theorem 3.7 — under strict limiting exactness, cluster points of $\varepsilon^\nu$-minimizers of the approximating problems solve the actual problem
-- statement:
--   Let $\varphi : \mathbb R^n \to \overline{\mathbb R}$ with $\operatorname{dom}\varphi \ne \emptyset$, let $f^\nu : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ ($\nu \in \mathbb N$), $\bar y \in \mathbb R^m$, $y^\nu \to \bar y$, and $\varepsilon^\nu \ge 0$ with $\varepsilon^\nu \to 0$ (in particular any $\varepsilon^\nu \searrow 0$). Let
--
--   $$
--   (u^\nu, x^\nu) \in \varepsilon^\nu\text{-}\operatorname*{argmin}_{u,x}\bigl\{f^\nu(u,x) - \langle y^\nu, u\rangle\bigr\},
--   $$
--
--   and let $(\hat u, \hat x)$ be a cluster point of $\{(u^\nu,x^\nu)\}$. Then:
--
--   1. If $\{f^\nu\}$ are strictly limit-exact Rockafellians for the problem of minimizing $\varphi$, supported by $\bar y$, then
--   $$
--   \hat u = 0 \quad\text{and}\quad \hat x \in \operatorname*{argmin}_x \varphi(x).
--   $$
--   2. If $f$ is a Rockafellian for that problem, exact and supported by $\bar y$, and the $f^\nu$ epi-converge to $f$ (limiting exactness), then $(\hat u,\hat x)$ satisfies the optimality condition (3.5) with this $f$:
--   $$
--   (\hat u, \hat x) \in \operatorname*{argmin}_{u,x}\bigl\{f(u,x) - \langle\bar y, u\rangle\bigr\}.
--   $$
--
--   The approximating problems (3.7), built from the accessible $f^\nu$ and $y^\nu$, are thus in the limit equivalent to the actual problem, which is not accessible.
--
--   **Formalization Note** Epi-convergence is the sequential (3.8)–(3.9) (`PerspEpi.SeqEpiConv`, product topology); every argmin contains only points where the function is $< +\infty$; a cluster point is `MapClusterPt`.
--
--   Differences from the source:
--   - generalization: conclusion of the strict case: x̂ ∈ argmin_x φ(x) → û = 0 ∧ x̂ ∈ argmin_x φ(x); reason: the last line of the proof (p.37) concludes û = 0 too; the Lean conclusion implies the printed one
--   - reading: (û, x̂) satisfies the necessary optimality condition (3.5) with f furnished by the limit of {f^ν} → (û, x̂) ∈ argmin_{u,x} f(u, x) − ⟨ȳ, u⟩ for every Rockafellian f for φ, exact and supported by ȳ, to which the f^ν epi-converge; reason: the right-hand side of (3.5) with u⋆ = û, x⋆ = x̂, i.e. (A.2), which the proof says gives (3.5); a sequential epi-limit is unique, so 'every such f' is 'the limit f'
--   - generalization: ε^ν ↘ 0 → ε^ν ≥ 0 and ε^ν → 0 (not necessarily monotone); reason: the paper does not define ↘ and uses it elsewhere (lim_{α↘0}) for a limit from above; on every reading (from above, nonincreasing, strictly decreasing) ε^ν ≥ 0 and ε^ν → 0 hold, so the printed claim is an instance
--   - encoding: ℝᵐ × ℝⁿ, R̄, ⟨y, u⟩, dom φ = {φ < ∞}, ν ∈ ℕ = {1, 2, …}, cluster point → (Fin m → ℝ) × (Fin n → ℝ) (product topology), EReal, y ⬝ᵥ u, AubinLipschitz.effDom φ = {φ ≠ ⊤}, ν ∈ Lean's ℕ from 0, MapClusterPt; reason: Lean convention; same instances
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 3.7, p.9 (proof p.37)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_IsStrictlyLimitExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt
import Definitions.Def_PerspEpi_SeqEpiConv

open Filter Topology

namespace RockafellianRelax

/-- **Theorem 3.7 (convergence under limiting exactness).** Royset, Chen & Eckstrand,
arXiv:2204.04762v4, Theorem 3.7, p.9: "For the problem (3.1) of minimizing φ : ℝⁿ → R̄, suppose
that dom φ ≠ ∅ and that {fν : ℝᵐ × ℝⁿ → R̄, ν ∈ ℕ} are strictly limit-exact Rockafellians, supported
by ȳ ∈ ℝᵐ. Let yν → ȳ, εν ↘ 0, and (uν, xν) ∈ εν-argmin_{u,x} {fν(u, x) − ⟨yν, u⟩}. Then, every
cluster point (û, x̂) of {(uν, xν), ν ∈ ℕ} satisfies x̂ ∈ argmin_x φ(x). If strict limiting
exactness is replaced by limiting exactness, then (û, x̂) satisfies the necessary optimality
condition (3.5) with f : ℝᵐ × ℝⁿ → R̄ being furnished by the limit of {fν, ν ∈ ℕ}."

Conclusion (1): under strict limiting exactness, `û = 0` and `x̂ ∈ argmin φ` (`û = 0` is the last
line of the proof, p.37). Conclusion (2): for the exact epi-limit `f`, supported by `ȳ`,
`(û, x̂) ∈ argmin_{u,x} f(u, x) − ⟨ȳ, u⟩`, the right-hand side of (3.5) with `u⋆ = û`.

**Formalization Note.** `ℝᵐ × ℝⁿ` is `(Fin m → ℝ) × (Fin n → ℝ)` (product topology), `R̄` is
`EReal`, `⟨y, u⟩` is `y ⬝ᵥ u`, epi-convergence is the sequential (3.8)–(3.9)
(`PerspEpi.SeqEpiConv`), `εν ↘ 0` is relaxed to `εν ≥ 0 ∧ εν → 0` (the paper does not define `↘`; its use in
`lim_{α ↘ 0}`, p.15, is a limit from above, and every reading implies this relaxed form), every
`argmin` / `ε-argmin` carries the domain condition of p.6, and a cluster point is
`MapClusterPt (û, x̂) atTop (fun ν => (uν, xν))`. `ν` runs over Lean's `ℕ` from `0`. -/
theorem theorem_3_7 {m n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (hdom : (AubinLipschitz.effDom φ).Nonempty)
    (F : ℕ → (Fin m → ℝ) × (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (y : ℕ → Fin m → ℝ)
    (hy : Tendsto y atTop (𝓝 ybar)) (ε : ℕ → ℝ) (hε0 : ∀ ν, 0 ≤ ε ν)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℕ → (Fin m → ℝ) × (Fin n → ℝ))
    (hz : ∀ ν, z ν ∈ epsArgmin (tilt (F ν) (y ν)) (ε ν))
    (zhat : (Fin m → ℝ) × (Fin n → ℝ)) (hzhat : MapClusterPt zhat atTop z) :
    (IsStrictlyLimitExact F φ ybar → zhat.1 = 0 ∧ zhat.2 ∈ argmin φ) ∧
      (∀ f : (Fin m → ℝ) × (Fin n → ℝ) → EReal, IsExact f φ ybar →
        PerspEpi.SeqEpiConv F f → zhat ∈ argmin (tilt f ybar)) := by sorry

end RockafellianRelax
