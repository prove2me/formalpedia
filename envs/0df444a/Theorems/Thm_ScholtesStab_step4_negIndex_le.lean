-- Prove2me | Theorems.Thm_ScholtesStab_step4_negIndex_le
-- name    : ScholtesStab.step4_negIndex_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:06.68648+00:00
-- url     : https://prove2.me/theorems/34bc5490-5736-48a8-badc-260e2520bb9f
-- title:
--   Proof of Theorem 1, Step 4: negative index under enlarging the subspace
-- statement:
--   Let $B$ be a bilinear form on $\mathbb R^n$ and $\mathcal T\subseteq\mathcal T'$ linear subspaces. Then
--
--   $$
--   \operatorname{negIndex}(B,\mathcal T')\ \le\ \operatorname{negIndex}(B,\mathcal T)+\dim\mathcal T'-\dim\mathcal T .
--   $$
--
--   In Step 4 this is applied to $B=D^2L^{\mathcal S}(x^t)$, $\mathcal T=\mathcal T^t$ and $\mathcal T'=\mathcal T^{\mathcal S}_{x^t}$: $QI^{\mathcal S}_{t,\mathcal T^{\mathcal S}_{x^t}}\le\dim\mathcal T^{\mathcal S}_{x^t}-\dim\mathcal T^t+QI^{\mathcal S}_{t,\mathcal T^t}$, where $QI^{\mathcal S}_{t,\mathcal T}$ denotes the number of negative eigenvalues of $D^2L^{\mathcal S}(x^t)\restriction_{\mathcal T}$.
--
--   **Formalization Note** Stated additively, $\operatorname{negIndex}(B,\mathcal T')+\dim\mathcal T\le\operatorname{negIndex}(B,\mathcal T)+\dim\mathcal T'$.
--
--   Differences from the source:
--   - encoding: ℝⁿ, indices j = 1, …, κ → EuclideanSpace ℝ (Fin n), indices in Fin κ (0-based); reason: a relabelling of coordinates and indices; same instances
--   - encoding: number of negative eigenvalues of the restricted Hessian D²L↾𝒯 → negIndex: the largest dimension of a subspace of 𝒯 on which the Hessian form is negative definite; reason: by Sylvester's law of inertia the two numbers coincide for the symmetric Hessian, in any basis of 𝒯
--   - generalization: QIˢ_{t,𝒯ˢ_xᵗ} ≤ dim 𝒯ˢ_xᵗ − dim 𝒯ᵗ + QIˢ_{t,𝒯ᵗ} for B = D²Lˢ(xᵗ), 𝒯ᵗ ⊆ 𝒯ˢ_xᵗ → the same inequality for every bilinear form B on ℝⁿ and all subspaces T ≤ T'; reason: the printed inequality is the instance B = D²Lˢ(xᵗ), T = 𝒯ᵗ, T' = 𝒯ˢ_xᵗ, whose containment the page takes from (18) ("In view of Steps 3a) and 3b)"); the display's trailing identity "= n − αˢ_t − k⁺" combines Step 1 with Step 3a's standard-form objects 𝒯ᵗ and k⁺ (p.19), which exist only after the proof's WLOG reduction to (12)–(13), and is not part of this item
--   - encoding: dim 𝒯ˢ − dim 𝒯ᵗ → the inequality written with both dimensions added on the other side; reason: avoids truncated subtraction in ℕ; same statement since dim T ≤ dim T'
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, Proof of Theorem 1, Step 4, p.20 (first display)

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_negIndex

namespace ScholtesStab

/-- **Negative index under enlarging the subspace.** Lämmel–Shikhman, arXiv:2501.07383v2, Proof
of Theorem 1, Step 4, p.20: "In view of Steps 3a) and 3b), we conclude that for all t
sufficiently small: QIˢ_{t,𝒯ˢ_xᵗ} ≤ dim𝒯ˢ_xᵗ − dim𝒯ᵗ + QIˢ_{t,𝒯ᵗ} = n − αˢ_t − k⁺".

The linear-algebra fact behind the first inequality: for every bilinear form `B` on `ℝⁿ` and
subspaces `T ≤ T'`, `negIndex B T' ≤ negIndex B T + (dim T' − dim T)`, i.e.
`negIndex B T' + dim T ≤ negIndex B T + dim T'`.

**Formalization Note.** Stated for arbitrary `B` and `T ≤ T'`; the page applies it to
`B = D²Lˢ(xᵗ)`, `T = 𝒯ᵗ`, `T' = 𝒯ˢ_xᵗ`. `QIˢ_{t,T}` (p.19, Step 2: "the number of negative
eigenvalues of D²Lˢ(xᵗ)↾T") is `negIndex (D²Lˢ(xᵗ)) T`. Stated additively to avoid
natural-number subtraction. -/
theorem step4_negIndex_le {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ) (T T' : Submodule ℝ (E n))
    (hTT' : T ≤ T') :
    negIndex B T' + Module.finrank ℝ T ≤ negIndex B T + Module.finrank ℝ T' := by sorry

end ScholtesStab
