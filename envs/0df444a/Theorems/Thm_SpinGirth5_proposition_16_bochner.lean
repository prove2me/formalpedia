-- Prove2me | Theorems.Thm_SpinGirth5_proposition_16_bochner
-- name    : SpinGirth5.proposition_16_bochner
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:35.003821+00:00
-- url     : https://prove2.me/theorems/805923f1-9451-45dd-a08f-8769c361b28a
-- title:
--   Proposition 16 — Bochner identity: Poincaré for $\mathcal L$ iff $\mathcal L^2\succeq\gamma\mathcal L$ on $\mathbf 1^\perp$
-- statement:
--   Let $\mu$ be a probability distribution with full support on a finite set $\Omega$, and let $\mathcal L$ be a linear operator on $L^2(\mu)=(\mathbb R^\Omega,\langle\cdot,\cdot\rangle_\mu)$ which is self-adjoint, positive semidefinite, and whose kernel consists exactly of the constant functions. Then for every $\gamma\in\mathbb R$,
--   $$\Big(\gamma\langle f,f\rangle_\mu\le\langle f,\mathcal Lf\rangle_\mu\ \ \forall f\perp\mathbf 1\Big)\iff\Big(\gamma\langle f,\mathcal Lf\rangle_\mu\le\langle\mathcal Lf,\mathcal Lf\rangle_\mu\ \ \forall f\perp\mathbf 1\Big).$$
--   Equivalently,
--   $$\inf_{f\ne0,\ f\perp\mathbf 1}\frac{\langle f,\mathcal Lf\rangle_\mu}{\langle f,f\rangle_\mu}=\inf_{f\ne0,\ f\perp\mathbf 1}\frac{\langle\mathcal Lf,\mathcal Lf\rangle_\mu}{\langle f,\mathcal Lf\rangle_\mu}.$$
--   In the paper $\mathcal L=I-P$ for an irreducible reversible chain $P\succeq0$, and the same proof is applied to every irreducible weighted Laplacian $\sum_va_vL_v$. The right-hand side "sees" the graph through products $L_uL_w$, which is what makes the local-to-global argument of Theorem 20 possible.
--
--   Differences from the source:
--   - generalization: L = Id − P for an irreducible P ⪰ 0 reversible w.r.t. µ (and, p.14, every irreducible weighted dynamics) → any self-adjoint positive semidefinite linear 𝓛 on L²(µ) whose kernel is exactly the constants; reason: Id − P with P reversible, P ⪰ 0, P1 = 1, P irreducible has these properties, and so does every irreducible ∑_v a_v L_v (p.14)
--   - encoding: equality of the two infima → for every γ, the two Poincaré-type inequalities on 1⊥ are equivalent; reason: each infimum is the largest γ in its inequality (⟨f,𝓛f⟩ > 0 on 1⊥ ∖ {0}), so the equivalence for all γ is the equality of the infima
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Proposition 16, p.12; §2.5, p.14

import Mathlib
import Definitions.Def_mm_spectral

namespace SpinGirth5

/-- **Proposition 16** (Bochner identity), for an irreducible weighted Laplacian. Let `μ` be a
probability distribution with full support on a finite set `Ω`, and let `𝓛` be a linear operator
on `L²(μ)` that is self-adjoint, positive semidefinite, and whose kernel consists exactly of the
constant functions. Then for every `γ`,
`γ ⟨f, f⟩_μ ≤ ⟨f, 𝓛 f⟩_μ ∀ f ⊥ 1  ⟺  γ ⟨f, 𝓛 f⟩_μ ≤ ⟨𝓛 f, 𝓛 f⟩_μ ∀ f ⊥ 1`,
equivalently `inf_{f≠0, f⊥1} ⟨f,𝓛f⟩/⟨f,f⟩ = inf_{f≠0, f⊥1} ⟨𝓛f,𝓛f⟩/⟨f,𝓛f⟩`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Proposition 16, p.12, and §2.5, p.14 ("The proof of Proposition 16
applies verbatim to every such irreducible weighted dynamics").

**Formalization Note** The paper's case is `𝓛 = I − P` for an irreducible reversible chain
`P ⪰ 0`, and the weighted Laplacians `∑_v a_v L_v` of §2.5; all satisfy the hypotheses. Each
infimum is the largest `γ` in the corresponding inequality, so the equivalence for every `γ` is
the equality of the infima. -/
theorem proposition_16_bochner {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : Ω → ℝ)
    (hμpos : ∀ x, 0 < μ x) (hμsum : ∑ x, μ x = 1) (𝓛 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hsymm : ∀ f g, MarkovMixing.innerPi μ f (𝓛 g) = MarkovMixing.innerPi μ (𝓛 f) g)
    (hpsd : ∀ f, 0 ≤ MarkovMixing.innerPi μ f (𝓛 f))
    (hker : ∀ f, 𝓛 f = 0 ↔ ∃ c : ℝ, f = fun _ => c) (γ : ℝ) :
    (∀ f : Ω → ℝ, MarkovMixing.innerPi μ f (fun _ => 1) = 0 →
        γ * MarkovMixing.innerPi μ f f ≤ MarkovMixing.innerPi μ f (𝓛 f)) ↔
      (∀ f : Ω → ℝ, MarkovMixing.innerPi μ f (fun _ => 1) = 0 →
        γ * MarkovMixing.innerPi μ f (𝓛 f) ≤ MarkovMixing.innerPi μ (𝓛 f) (𝓛 f)) := by sorry

end SpinGirth5
