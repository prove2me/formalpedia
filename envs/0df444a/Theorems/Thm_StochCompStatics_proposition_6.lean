-- Prove2me | Theorems.Thm_StochCompStatics_proposition_6
-- name    : StochCompStatics.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:29.121366+00:00
-- url     : https://prove2.me/theorems/e8e93e9f-5bf1-4f82-96a7-fab78aa5a90b
-- title:
--   Proposition 6 — with $\Gamma$ ascending, $\max_{a\in\Gamma(s)}h(s,a,e,f)$ inherits increasing differences in $(s,e)$
-- statement:
--   Let $(E,\succeq)$ be a partially ordered set, $S$ a partially ordered set, $A\subseteq\mathbb R$, and $\Gamma$ an ascending correspondence with $\Gamma(s)\subseteq A$. Let $\varphi(s,a,e)$ (the paper's $h(s,a,e,f)$ for a fixed $f$) have increasing differences in $(s,a)$ on $S\times A$, in $(s,e)$ on $S\times E$ and in $(a,e)$ on $A\times E$, and assume the maximum of $\varphi(s,\cdot,e)$ over $\Gamma(s)$ is attained for every $(s,e)$. Then
--   $$
--   Tf(s,e)=\max_{a\in\Gamma(s)}\varphi(s,a,e)
--   $$
--   has increasing differences in $(s,e)$.
--
--   This is the step that carries increasing differences through one application of the Bellman operator; the paper refers to Hopenhayn and Prescott (1992), Lemma 1, and Lovejoy (1987), Lemma 2.
--
--   Differences from the source:
--   - generalization: h(s, a, e, f) = r(s, a, e) + β∫ f(s′, e)p(s, a, ds′) for a fixed f → an arbitrary function φ : S → ℝ → E → ℝ; reason: the proposition uses only the three increasing-differences properties of h; h is an instance
--   - generalization: S ⊆ ℝⁿ with the componentwise order → any partially ordered set S; reason: the paper's S is an instance
--   - encoding: increasing differences in (s, a), (s, e), (a, e) → on S × A for each e, on S × E for each a ∈ A, on A × E for each s, with Γ(s) ⊆ A; reason: the domains of h; same instances
--   - encoding: Tf(s) = max_{a∈Γ(s)} h(s, a, f) → bellman = sSup of the image h(s, Γ(s), f), with the attainment of the maximum as a hypothesis wherever the paper writes max; reason: the paper's max presupposes attainment; sSup equals the maximum when it is attained
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, Proposition 6, p.21 (Appendix §6.2)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_StochCompStatics_Model

namespace StochCompStatics

open Supermodularity.Monotonicity

/-- Proposition 6 (Light, Stochastic Comparative Statics in Markov Decision Processes,
arXiv:1904.05481v2, Appendix §6.2, p.21): let `(E, ⪰)` be a partially ordered set and `Γ(s)`
ascending. If `h(s, a, e, f)` has increasing differences in `(s, a)`, `(s, e)` and `(a, e)`, then
`Tf(s, e) = max_{a ∈ Γ(s)} h(s, a, e, f)` has increasing differences in `(s, e)`.

**Formalization Note** The function `φ(s, a, e)` stands for `h(s, a, e, f)` with `f` fixed; the
statement holds for every such `φ`. Increasing differences in `(s, a)` are required on `S × A` for
each `e`, in `(s, e)` on `S × E` for each `a ∈ A`, and in `(a, e)` on `A × E` for each `s`, where
`Γ(s) ⊆ A`. The maximum is `sSup` of the image, and its attainment at every `(s, e)` is assumed,
as the paper's `max` presupposes. -/
theorem proposition_6 {S : Type*} [PartialOrder S] {E : Type*} [PartialOrder E] (A : Set ℝ)
    (Γ : S → Set ℝ) (φ : S → ℝ → E → ℝ) (hΓA : ∀ s, Γ s ⊆ A) (hasc : IsAscending Γ)
    (hsa : ∀ e, IncreasingDifferencesOn (fun s a => φ s a e) (Set.univ ×ˢ A))
    (hse : ∀ a ∈ A, IncreasingDifferencesOn (fun s e => φ s a e) Set.univ)
    (hae : ∀ s, IncreasingDifferencesOn (fun a e => φ s a e) (A ×ˢ Set.univ))
    (hmax : ∀ s e, ∃ a ∈ Γ s, IsGreatest ((fun b => φ s b e) '' Γ s) (φ s a e)) :
    IncreasingDifferencesOn (fun s e => sSup ((fun a => φ s a e) '' Γ s)) Set.univ := by sorry

end StochCompStatics
