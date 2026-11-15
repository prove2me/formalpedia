-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_proposition_22
-- name    : UniversalNonstochastic.Main.Supplement.proposition_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:33:00.179014+00:00
-- url     : https://prove2.me/theorems/c6d14823-30b6-4348-9f60-ee19f87308f7
-- title:
--   Proposition 22 — two extreme bounds for any deficiency
-- statement:
--   Let $d$ be a deficiency (a lower semicomputable function $d(\omega\mid Q)\in(-\infty,\infty]$ of an object and an elementary probability measure), and $N_{\alpha,\beta}(d)$ the set of objects for which no elementary $Q$ has $K(Q)\le\alpha$ and $d(\omega\mid Q)\le\beta$.
--
--   1. If $d(\omega\mid Q)=\infty$ whenever $Q(\{\omega\})=0$, there is $c_{41}>0$ such that $\mathbf m(N_{\alpha,\beta}(d))\ge2^{-\alpha-c_{41}}$ for all $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$.
--   2. If $d(\omega\mid\delta_\omega)\le c_{42}$ for all $\omega$, where $c_{42}$ is a constant and $\delta_\omega$ the point mass at $\omega$, there is $c_{43}>0$ such that
--   $$\mathbf m(N_{\alpha,\beta}(d))\le c_{43}\,\tau(\alpha)$$
--   for all $\alpha\in\mathbb N_0$ and all $\beta\in[0,\infty)$ with $\beta\ge c_{42}$.
--
--   All deficiencies of the paper satisfy both conditions; the proposition is used in Theorems 11, 13 and 14.
--
--   Differences from the source:
--   - encoding: the point mass δ_ω → the published uniform probability measure on {ω}; reason: the uniform measure on a singleton is the point mass
--   - encoding: for all α and β (part 1), for all α and all β ≥ c42 (part 2) → α ∈ ℕ₀ with 0 ≤ β (part 1), and 0 ≤ β ∧ c42 ≤ β (part 2); reason: N_{α,β}(d) is defined only for α ∈ ℕ₀ and β ∈ [0, ∞) (p.10), so the bound 0 ≤ β only excludes undefined cases
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Proposition 22, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels

namespace UniversalNonstochastic.Main.Supplement

/-- Proposition 22, p.22: let `d` be a deficiency.
1. If `d(ω | Q) = ∞` whenever `Q({ω}) = 0`, there is `c₄₁ > 0` with
   `m(N_{α,β}(d)) ≥ 2^{-α-c₄₁}` for all `α ∈ ℕ₀` and `β ∈ [0, ∞)`.
2. If `d(ω | δ_ω) ≤ c₄₂` for all `ω` (`δ_ω` the point mass, i.e. the uniform measure on `{ω}`),
   there is `c₄₃ > 0` with `m(N_{α,β}(d)) ≤ c₄₃ τ(α)` for all `α` and all `β ≥ c₄₂`. -/
theorem proposition_22 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder)
    (d : ℕ+ → ElemMeasure → EReal) (hd : IsDeficiency d) :
    ((∀ (ω : ℕ+) (Q : ElemMeasure), Q.w ω = 0 → d ω Q = ⊤) →
      ∃ c₄₁ : ℝ, 0 < c₄₁ ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
        (2 : ℝ) ^ (-(α : ℝ) - c₄₁) ≤ mass m (nonQuasiStochastic U d α β)) ∧
    ∀ c₄₂ : ℝ, (∀ ω : ℕ+, d ω (uniform {ω} (Finset.singleton_nonempty ω)) ≤ ((c₄₂ : ℝ) : EReal)) →
      ∃ c₄₃ : ℝ, 0 < c₄₃ ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β → c₄₂ ≤ β →
        mass m (nonQuasiStochastic U d α β) ≤ c₄₃ * tail m (α : ℝ) := by sorry

end UniversalNonstochastic.Main.Supplement
