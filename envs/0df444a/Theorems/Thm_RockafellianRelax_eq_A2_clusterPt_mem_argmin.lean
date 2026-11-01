-- Prove2me | Theorems.Thm_RockafellianRelax_eq_A2_clusterPt_mem_argmin
-- name    : RockafellianRelax.eq_A2_clusterPt_mem_argmin
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:20.076869+00:00
-- url     : https://prove2.me/theorems/45ff8bfc-8bb1-4d2f-87d5-86310004a409
-- title:
--   (A.2), proof of Theorem 3.7 — cluster points of $\varepsilon^\nu$-minimizers of epi-convergent functions minimize the limit
-- statement:
--   Let $\alpha$ be a first-countable topological space, and let $\psi^\nu, \psi : \alpha \to \overline{\mathbb R}$ with $\psi^\nu$ epi-converging to $\psi$ (in the sense of (3.8)–(3.9)) and $\operatorname{dom}\psi \ne \emptyset$. Let $\varepsilon^\nu \ge 0$ with $\varepsilon^\nu \to 0$, and
--
--   $$
--   z^\nu \in \varepsilon^\nu\text{-}\operatorname*{argmin}\psi^\nu \qquad (\nu \in \mathbb N).
--   $$
--
--   Then every cluster point $\hat z$ of $\{z^\nu\}$ satisfies
--
--   $$
--   \hat z \in \operatorname*{argmin}\psi ,
--   $$
--
--   in particular $\psi(\hat z) < \infty$. No properness of $\psi$ is assumed: $\psi$ may take the value $-\infty$. In the paper this is applied with $\alpha = \mathbb R^m \times \mathbb R^n$, $\psi^\nu = \tilde f^\nu$, $\psi = \tilde f$, where $\operatorname{dom}\tilde f \ne \emptyset$ follows from $\operatorname{dom}\varphi \ne \emptyset$.
--
--   Differences from the source:
--   - generalization: ℝᵐ × ℝⁿ, the tilted functions f̃^ν, f̃ of the proof, with f̃ ≢ ∞ deduced from dom φ ≠ ∅ → any first-countable topological space α, any ψ^ν epi-converging to ψ, with dom ψ ≠ ∅; reason: ℝᵐ × ℝⁿ is first countable and f̃(0, x) = φ(x), so the paper's case is an instance
--   - generalization: cases (i) f̃ proper ([59, Theorem 5.5(b)]) and (ii) f̃ takes −∞ somewhere, treated separately → one statement with no properness assumption; reason: cases (i) and (ii) together cover every f̃ with dom f̃ ≠ ∅; the conclusion (A.2) is the same in both
--   - generalization: ε^ν ↘ 0 → ε^ν ≥ 0 and ε^ν → 0 (not necessarily monotone); reason: a nonincreasing sequence tending to 0 is such a sequence
--   - encoding: R̄, dom ψ = {ψ < ∞}, cluster point of {z^ν, ν ∈ ℕ} → EReal, AubinLipschitz.effDom ψ = {ψ ≠ ⊤}, MapClusterPt ẑ atTop z, ν ∈ Lean's ℕ from 0; reason: Lean convention; same instances
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proof of Theorem 3.7, display (A.2), p.37

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_PerspEpi_SeqEpiConv

open Filter Topology

namespace RockafellianRelax

/-- **Cluster points of approximate minimizers of epi-convergent functions minimize the limit**,
display (A.2). Royset, Chen & Eckstrand, arXiv:2204.04762v4, Proof of Theorem 3.7, display (A.2),
p.37: "We consider three cases. (i) If f̃ is proper, then [59, Theorem 5.5(b)] applies and we
conclude that (û, x̂) ∈ argmin_{u,x} f̃(u, x). (A.2) (ii) If f̃ takes the value −∞ at one or more
points, then the arguments in the proof of [59, Theorem 5.5(a,b)] carry over and we again conclude
that (A.2) holds. (iii) The case f̃ being identical to ∞ is ruled out by the assumption dom φ ≠ ∅."

Let `ψν` epi-converge to `ψ`, with `dom ψ ≠ ∅`, let `εν ≥ 0` with `εν → 0` and
`zν ∈ εν-argmin ψν`. Then every cluster point `ẑ` of `(zν)` lies in `argmin ψ`.

**Formalization Note.** Stated on any first-countable topological space `α` (the paper's case is
`α = ℝᵐ × ℝⁿ` with `ψν = f̃ν`, `ψ = f̃`); cases (i) and (ii) are covered at once, without
properness, and case (iii) is the hypothesis `dom ψ ≠ ∅`. `argmin` requires `ψ(ẑ) < +∞`. A cluster
point is `MapClusterPt ẑ atTop z`. -/
theorem eq_A2_clusterPt_mem_argmin {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (Ψ : ℕ → α → EReal) (ψ : α → EReal) (hepi : PerspEpi.SeqEpiConv Ψ ψ)
    (hdom : (AubinLipschitz.effDom ψ).Nonempty) (ε : ℕ → ℝ) (hε0 : ∀ ν, 0 ≤ ε ν)
    (hε : Tendsto ε atTop (𝓝 0)) (z : ℕ → α) (hz : ∀ ν, z ν ∈ epsArgmin (Ψ ν) (ε ν))
    (zhat : α) (hzhat : MapClusterPt zhat atTop z) :
    zhat ∈ argmin ψ := by sorry

end RockafellianRelax
