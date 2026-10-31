-- Prove2me | Theorems.Thm_SweepingDesing_proposition_20
-- name    : SweepingDesing.proposition_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:34.568548+00:00
-- url     : https://prove2.me/theorems/96fb03f6-ef2a-452c-a75f-fbbb84703d05
-- title:
--   Proposition 20 — concatenation of local curves into a piecewise absolutely continuous curve
-- statement:
--   Let $a<b$ and let $\Gamma$ be a collection of absolutely continuous curves, each defined on some nontrivial interval $J\subset(a,b)$ with values in $\mathbb R^n$. Assume that for each $t\in(a,b)$ there are $\varepsilon_t>0$ and $\gamma_t\in\Gamma$ with $\operatorname{dom}(\gamma_t)=[t,t+\varepsilon_t)$. Then there exist
--
--   1. a countable partition $\{I_k\}_{k\in\mathbb N}$ of $(a,b)$ into pairwise disjoint intervals $I_k$ with nonempty interior, and
--   2. a piecewise absolutely continuous curve $\gamma:(a,b)\to\mathbb R^n$
--
--   such that for each $k$ there is $\gamma^k\in\Gamma$ with $I_k\subseteq\operatorname{dom}(\gamma^k)$ and $\gamma=\gamma^k$ on $I_k$.
--
--   The proof of Theorem A glues orbits that are almost as fast as the oriented talweg into one long piecewise orbit.
--
--   Differences from the source:
--   - reading: absolutely continuous on a (possibly non-compact) interval I → absolutely continuous on every compact interval [c, d] ⊆ I (IsLocallyAC); reason: the usual W^{1,1}_loc reading for [t, t+δ), [a, b), (a, b) and the pieces J_i; on a compact interval it is absolute continuity on I
--   - encoding: a collection Γ of curves γ with domains J → Γ is a set of pairs (γ, J) with γ : ℝ → ℝⁿ, J a nontrivial interval ⊆ (a, b) and γ absolutely continuous on J; reason: the domain of a curve is part of the data (dom(γ_t) = [t, t + ε_t))
--   - reading: a piecewise absolutely continuous curve γ : (a, b) → ℝ with γ = γⁿ on I_n → γ : ℝ → ℝⁿ piecewise absolutely continuous on (a, b), with I_n ⊆ dom(γⁿ) and γ = γⁿ on I_n; reason: the printed codomain ℝ is a typo: every curve of Γ is ℝⁿ-valued and γ agrees with them; γ = γⁿ on I_n presupposes that γⁿ is defined there
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 20, p.14

import Mathlib
import Definitions.Def_SweepingDesing_IsLocallyAC
import Definitions.Def_SweepingDesing_IsPAC
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 20, p.14 (concatenation): let `b > a` and let `Γ` be a collection of
absolutely continuous curves `γ` defined in some nontrivial interval `J ⊂ (a, b)` with values in
`ℝⁿ`. Assume that for each `t ∈ (a, b)` there exist `ε_t > 0` and `γ_t ∈ Γ` with
`dom(γ_t) = [t, t + ε_t)`. Then there exist a countable partition `{I_n}_{n ∈ ℕ}` of `(a, b)` into
intervals `I_n` of nonempty interior and a piecewise absolutely continuous curve
`γ : (a, b) → ℝⁿ` such that for each `n ∈ ℕ` there is `γⁿ ∈ Γ` with `γ = γⁿ` on `I_n`.

**Formalization Note** A curve of `Γ` is a pair `(γ, J)` of a map `ℝ → ℝⁿ` and its domain `J`
(a nontrivial interval inside `(a, b)` on whose compact subintervals `γ` is absolutely
continuous). The printed codomain `ℝ` of the glued curve is a typo for `ℝⁿ`. "`γ = γⁿ` on `I_n`"
includes `I_n ⊆ dom(γⁿ)`. The partition is an `ℕ`-indexed family of pairwise disjoint intervals. -/
theorem proposition_20 {n : ℕ} (a b : ℝ) (hab : a < b) (Γ : Set ((ℝ → EuclideanSpace ℝ (Fin n)) × Set ℝ))
    (hΓ : ∀ p ∈ Γ, p.2 ⊆ Ioo a b ∧ p.2.OrdConnected ∧ (interior p.2).Nonempty ∧ IsLocallyAC p.1 p.2)
    (hcover : ∀ t ∈ Ioo a b, ∃ ε > (0 : ℝ), ∃ γ : ℝ → EuclideanSpace ℝ (Fin n), (γ, Ico t (t + ε)) ∈ Γ) :
    ∃ I : ℕ → Set ℝ, (∀ k, (I k).OrdConnected ∧ (interior (I k)).Nonempty) ∧
      Pairwise (fun i j => Disjoint (I i) (I j)) ∧ (⋃ k, I k) = Ioo a b ∧
      ∃ γ : ℝ → EuclideanSpace ℝ (Fin n), IsPAC γ (Ioo a b) ∧
        ∀ k, ∃ p ∈ Γ, I k ⊆ p.2 ∧ EqOn γ p.1 (I k) := by sorry

end SweepingDesing
