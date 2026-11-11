-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_4_3
-- name    : PottsCIZeroFree.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:33.218201+00:00
-- url     : https://prove2.me/theorems/dae28e8c-c26f-4e5f-ba63-37a5089eaced
-- title:
--   Lemma 4.3 — finite-state continuity of normalized laws as $x\downarrow0$
-- statement:
--   Let $\Omega$ be finite and let $w^{(0)}_x,w^{(1)}_x$ ($x\ge0$) be two families of nonnegative weights on $\Omega$, continuous at $x=0$, with positive total weights at $x=0$. Let $\mu^{(i)}_x=w^{(i)}_x/\sum_\omega w^{(i)}_x(\omega)$ be the normalized laws. Then $\mu^{(0)}_x,\mu^{(1)}_x$ converge in total variation to $\mu^{(0)}_0,\mu^{(1)}_0$ as $x\downarrow0$, and for every metric $d$ on $\Omega$
--   $$W_{1,d}(\mu^{(0)}_x,\mu^{(1)}_x)\longrightarrow W_{1,d}(\mu^{(0)}_0,\mu^{(1)}_0)\qquad(x\downarrow0).$$
--   Consequently, if $W_{1,d}(\mu^{(0)}_x,\mu^{(1)}_x)\le B(x)$ for all small $x>0$, then
--   $$W_{1,d}(\mu^{(0)}_0,\mu^{(1)}_0)\le\liminf_{x\downarrow0}B(x).$$
--
--   This passes coupling bounds proved at positive activity to the hard-constraint endpoint.
--
--   **Formalization Note** Total variation is the published `MarkovMixing.tvDist`, and $W_{1,d}$ is `transportDist`. A metric is a function with the four metric axioms. The $\liminf$ is taken in `EReal`, so it is meaningful for every $B:\mathbb R\to\mathbb R$.
--
--   Differences from the source:
--   - generalization: weights continuous at x = 0 → weights continuous at 0 within [0, ∞) (from the right); reason: only x ↓ 0 enters; continuity at 0 implies right continuity, so the source’s hypothesis is a special case
--   - encoding: families of nonnegative weights indexed by small x ≥ 0 → w : ℝ → Ω → ℝ, nonnegative for x ≥ 0; reason: a family on [0, x₀] extends to x ≥ 0 by a constant without changing any limit as x ↓ 0
--   - encoding: lim inf_{x↓0} B(x) → Filter.liminf of B cast to EReal along 𝓝[>] 0; reason: the real lim inf of an unbounded B is a junk value in Lean; EReal keeps ±∞
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.17 (PDF p.19), Lemma 4.3

import Mathlib
import Definitions.Def_mm_transport

open Classical

namespace PottsCIZeroFree

/-- Lemma 4.3 (Finite-state continuity of normalized laws) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.17
(PDF p.19). On a finite space `Ω`, let two families of nonnegative weights be continuous at
`x = 0`, with positive total weights there. Their normalized laws `µ^{(0)}_x, µ^{(1)}_x`
converge in total variation to `µ^{(0)}_0, µ^{(1)}_0` as `x ↓ 0`, and for every metric `d` on
`Ω`, `W_{1,d}(µ^{(0)}_x, µ^{(1)}_x) → W_{1,d}(µ^{(0)}_0, µ^{(1)}_0)`. Consequently, if
`W_{1,d}(µ^{(0)}_x, µ^{(1)}_x) ≤ B(x)` for all small `x > 0`, then
`W_{1,d}(µ^{(0)}_0, µ^{(1)}_0) ≤ lim inf_{x↓0} B(x)`.

**Formalization Note.** The weights are given for `x ≥ 0`; continuity at `0` is from the right
(`x ↓ 0`). A metric is a function with the four metric axioms. The `lim inf` is taken in
`EReal`, so it is meaningful for every `B : ℝ → ℝ`. -/
theorem lemma_4_3 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (w₀ w₁ : ℝ → Ω → ℝ)
    (hnn₀ : ∀ x, 0 ≤ x → ∀ ω, 0 ≤ w₀ x ω) (hnn₁ : ∀ x, 0 ≤ x → ∀ ω, 0 ≤ w₁ x ω)
    (hc₀ : ∀ ω, ContinuousWithinAt (fun x => w₀ x ω) (Set.Ici 0) 0)
    (hc₁ : ∀ ω, ContinuousWithinAt (fun x => w₁ x ω) (Set.Ici 0) 0)
    (hpos₀ : 0 < ∑ ω, w₀ 0 ω) (hpos₁ : 0 < ∑ ω, w₁ 0 ω) :
    let μ₀ : ℝ → Ω → ℝ := fun x ω => w₀ x ω / ∑ ω', w₀ x ω'
    let μ₁ : ℝ → Ω → ℝ := fun x ω => w₁ x ω / ∑ ω', w₁ x ω'
    Filter.Tendsto (fun x => MarkovMixing.tvDist (μ₀ x) (μ₀ 0)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) ∧
      Filter.Tendsto (fun x => MarkovMixing.tvDist (μ₁ x) (μ₁ 0)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) ∧
      ∀ d : Ω → Ω → ℝ, (∀ a, d a a = 0) → (∀ a b, d a b = 0 → a = b) →
        (∀ a b, d a b = d b a) → (∀ a b c, d a c ≤ d a b + d b c) →
        Filter.Tendsto (fun x => MarkovMixing.transportDist d (μ₀ x) (μ₁ x))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (MarkovMixing.transportDist d (μ₀ 0) (μ₁ 0))) ∧
          ∀ B : ℝ → ℝ,
            (∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), MarkovMixing.transportDist d (μ₀ x) (μ₁ x) ≤ B x) →
            ((MarkovMixing.transportDist d (μ₀ 0) (μ₁ 0) : ℝ) : EReal) ≤
              Filter.liminf (fun x => ((B x : ℝ) : EReal)) (nhdsWithin 0 (Set.Ioi 0)) := by sorry

end PottsCIZeroFree
