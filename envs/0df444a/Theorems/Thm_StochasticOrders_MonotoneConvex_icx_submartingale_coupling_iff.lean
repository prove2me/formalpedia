-- Prove2me | Theorems.Thm_StochasticOrders_MonotoneConvex_icx_submartingale_coupling_iff
-- name    : StochasticOrders.MonotoneConvex.icx_submartingale_coupling_iff
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:58.667982+00:00
-- url     : https://prove2.me/theorems/76c76a50-81f9-4acc-a0d7-e567fef4c2ab
-- title:
--   Theorem 4.A.5 (increasing convex case) — submartingale-coupling characterization of the increasing convex order
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be random variables. Then
--
--   $$X \le_{icx} Y \iff \exists\,(\Omega'',\rho),\ \hat X,\hat Y:\Omega''\to\mathbb{R} \text{ with }
--     \hat X =_{st} X,\ \hat Y =_{st} Y,\ \text{and } \{\hat X,\hat Y\} \text{ a submartingale},$$
--
--   i.e. $E[\hat Y \mid \hat X] \ge \hat X$ a.s. **Furthermore**, $\hat X$ and $\hat Y$ can be
--   selected such that $[\hat Y \mid \hat X = x]$ is increasing in $x$ in the usual stochastic
--   order $\le_{st}$. This is the increasing-convex analogue of Chunk 03's Strassen martingale
--   coupling for the plain convex order (Theorem 3.A.4): the book states "the proof of this
--   theorem is similar," and calls the constructive part "not easy to prove" — no proof is
--   attempted here. The easy direction (existence $\implies$ $X\le_{icx}Y$) follows from Jensen's
--   inequality applied twice, exactly as in the convex-order case.
--
--   **Formalization Note** As in Chunk 03's `convex_order_martingale_coupling_iff`: "$\hat X
--   =_{st} X$" is `ProbabilityTheory.IdentDistrib`; "$E[\hat Y\mid\hat X]\ge\hat X$ a.s." is
--   Mathlib's conditional-expectation notation `X̂ ≤ᵐ[ρ] ρ[Ŷ | m]` with `m` the σ-algebra generated
--   by `X̂`; the "Furthermore" clause is folded into the same existential witness via
--   `ProbabilityTheory.condDistrib`, restated as the conditional-distribution kernel's survival
--   function being monotone in `x` at every threshold — the same shape Chunk 01's `UsualOrder`
--   uses, restated locally since drafts cannot import another mission's definitions. This chapter
--   states the increasing convex and increasing concave cases of Theorem 4.A.5 as **two separate**
--   theorems (this one and `icv_supermartingale_coupling_iff`) rather than one Lean statement
--   conflated with an `Or`, since the submartingale/supermartingale conditions are not symmetric
--   rewrites of each other — the swapped roles of `X̂`/`Ŷ` in the conditioning is a genuinely
--   different predicate shape between the two cases, not merely a flipped inequality (per this
--   chapter's own pitfall warning).
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 183, Theorem 4.A.5

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory ProbabilityTheory

/-- Theorem 4.A.5 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 183), increasing
convex case: `X ≤icx Y` if, and only if, there exist two random variables `X̂` and `Ŷ`, defined on
the same probability space, such that `X̂ =st X`, `Ŷ =st Y`, and `{X̂, Ŷ}` is a submartingale, that
is, `E[Ŷ | X̂] ≥ X̂` a.s. Furthermore, `X̂` and `Ŷ` can be selected such that `[Ŷ | X̂ = x]` is
increasing in `x` in the usual stochastic order `≤st`. -/
theorem icx_submartingale_coupling_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) :
    IcxOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] ∧
        (∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ,
          (condDistrib Yhat Xhat ρ x₁) {y : ℝ | t < y} ≤
            (condDistrib Yhat Xhat ρ x₂) {y : ℝ | t < y}) := by sorry

end StochasticOrders.MonotoneConvex
