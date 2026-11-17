-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_5_7
-- name    : RQCMoments.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:51:04.714189+00:00
-- url     : https://prove2.me/theorems/ae2e9382-c9aa-41c5-a534-3aee31331931
-- title:
--   Theorem 5.7 — the largest Gauss weight of $\mathrm{Beta}(1,D)$ is $\Omega(\sqrt{D/(\ell(\ell+D))})$
-- statement:
--   For integers $D\ge1$ and $\ell\ge2$, let $0<x_1<x_2<\dots<x_\ell<1$ be the Gaussian quadrature points of $\mathrm{Beta}(1,D)$ and $w_1,\dots,w_\ell$ the corresponding weights. Then
--
--   $$\max_{i\in[\ell]}w_i=\Omega\Big(\sqrt{\tfrac{D}{\ell(\ell+D)}}\Big).$$
--
--   That is, there is an absolute constant $c>0$ such that some weight satisfies $w_i\ge c\sqrt{D/(\ell(\ell+D))}$.
--
--   This matches the upper bound of Theorem 4.4 (base mission) up to a constant, so the maximal Gauss weight of $\mathrm{Beta}(1,D)$ is $\Theta(\sqrt{D/(\ell(\ell+D))})$.
--
--   **Formalization Note** The Gauss rule is the published `RQCMoments.IsGaussRule` (strictly increasing nodes, exactness with integrability on real polynomials of degree $\le2\ell-1$), which determines the nodes and weights uniquely; that the nodes lie in $(0,1)$ is a property of the rule, not a hypothesis. $c$ is chosen before $D$, $\ell$ and the rule.
--
--   Differences from the source:
--
--   - encoding: max_i w_i = Ω(√(D/(ℓ(ℓ+D)))) → ∃ c > 0 (before D, ℓ, the rule) and some i with c·√(D/(ℓ(ℓ+D))) ≤ w_i; reason: asymptotic notation with absolute constants chosen first; same content
--   - encoding: the Gaussian quadrature points and weights of Beta(1, D) → any (x, w) with IsGaussRule (betaMeasure 1 D) ℓ x w; reason: the ℓ-node Gauss rule is unique, so this is the paper rule
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 5.7, (128), p.35 (PDF p.37); §4.1, p.21

import Mathlib
import Definitions.Def_RQCMoments_IsGaussRule

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 5.7** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 5.7, (128), p.35, PDF p.37).
For integers `D ≥ 1` and `ℓ ≥ 2`, let `0 < x₁ < ⋯ < x_ℓ < 1` be the Gaussian quadrature points of
`Beta(1, D)` and `w₁, …, w_ℓ` the corresponding weights. Then
`max_{i∈[ℓ]} wᵢ = Ω(√(D/(ℓ(ℓ+D))))`.

**Formalization Note** The `Ω(·)` is one absolute constant `c > 0` chosen before `D`, `ℓ` and the
rule. The Gauss rule is the published `RQCMoments.IsGaussRule` (strictly increasing nodes, exact
with integrability on real polynomials of degree `≤ 2ℓ − 1`), which determines the paper's nodes and
weights uniquely; that the nodes lie in `(0,1)` is a property of the rule, not a hypothesis.
`Beta(1, D)` is Mathlib's `betaMeasure 1 D`. "`max wᵢ ≥ c·…`" is "some `wᵢ` is `≥ c·…`". -/
theorem theorem_5_7 :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 1 ≤ D → ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ x w : Fin ℓ → ℝ,
      IsGaussRule (ProbabilityTheory.betaMeasure 1 D) ℓ x w →
        ∃ i, c * Real.sqrt ((D : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) + D))) ≤ w i := by sorry

end Supplement

end RQCMoments
