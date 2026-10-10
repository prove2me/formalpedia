-- Prove2me | Theorems.Thm_WassMMSE_FW_lemma_6_3_i
-- name    : WassMMSE.FW.lemma_6_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:01.943993+00:00
-- url     : https://prove2.me/theorems/cb2e871d-40ca-481c-a760-4b9fd4814d04
-- title:
--   Lemma 6.3 (i), p. 24 — for convex f the surrogate duality gap satisfies g ≥ δ(f(s) − f⋆)
-- statement:
--   Let $\mathcal S=\times_k\mathcal S^{[k]}$ be a product of convex compact sets, let $f$ be convex on $\mathcal S$ and differentiable at its points, with optimal value $f^\star=\min_{s\in\mathcal S}f(s)$, and let $F$ be an inexact oracle with precision $\delta\in[0,1]$ in the sense of (6.2). For $s\in\mathcal S$ let $d=F(s)-s$ and let $g=-d^\top\nabla f(s)$ be the surrogate duality gap. Then
--
--   $$g\ge\delta\,\big(f(s)-f^\star\big).$$
--
--   The gap computed by the oracle thus certifies a fixed fraction of the current suboptimality; this gives the contraction factor $1-\delta/2$ in case (i) of the proof of Theorem 6.2.
--
--   **Formalization Note** $f^\star$ is a real number that is the least element of $f(\mathcal S)$, so the minimum is attained, as (6.1) writes it.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 24, Lemma 6.3 (i)

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- Lemma 6.3 (i), p. 24: for convex `f`, the surrogate duality gap at any `s ∈ 𝒮` satisfies
`g ≥ δ (f(s) − f⋆)`, where `f⋆ = min_{s ∈ 𝒮} f(s)`. -/
theorem lemma_6_3_i
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {fstar : ℝ} (hfstar : IsLeast (f '' S) fstar) {s : BlockSpace K d} (hs : s ∈ S) :
    δ * (f s - fstar) ≤ fwGap f F s := by sorry

end WassMMSE.FW
