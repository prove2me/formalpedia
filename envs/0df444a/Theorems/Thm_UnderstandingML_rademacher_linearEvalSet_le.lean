-- Prove2me | Theorems.Thm_UnderstandingML_rademacher_linearEvalSet_le
-- name    : UnderstandingML.rademacher_linearEvalSet_le
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-26T16:19:35.984905+00:00
-- url     : https://prove2.me/theorems/c405af35-9f2f-4b92-9895-3211e39528ba
-- title:
--   Lemma 26.10: R(H₂∘S) ≤ B·maxᵢ‖xᵢ‖/√m for the ℓ₂ ball of radius B
-- statement:
--   **Lemma 26.10.** Let $x_1,\dots,x_m$ be vectors in a real inner product space (a Hilbert space in the book), let $B\ge0$, and let
--
--   $$H_2\circ S=\big\{(\langle w,x_1\rangle,\dots,\langle w,x_m\rangle):\ \|w\|\le B\big\}\subseteq\mathbb{R}^m .$$
--
--   Then
--
--   $$R(H_2\circ S)\le\frac{B\,\max_i\|x_i\|}{\sqrt m}.$$
--
--   Here $R(A)=\frac1m\mathbb{E}_\sigma\sup_{a\in A}\sum_i\sigma_ia_i$ is the Rademacher complexity (26.5), with $\sigma$ uniform on $\{\pm1\}^m$. Combined with the contraction lemma, this lemma gives the dimension-free bound $2\rho BR/\sqrt m$ in Theorem 26.12 for linear predictors with Lipschitz losses.
--
--   **Formalization Note** The book states the case $B=1$. The statement here is for the class $\{w:\|w\|\le B\}$ with $B\ge0$ (the set `linearEvalSet B x` of the mission's definitions), which is the form used in §26.3. For $m=0$ both sides are $0$ by Lean's conventions.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Chapter 26, Lemma 26.10 (p. 382)

import Definitions.Def_UnderstandingML_Rademacher

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 26.10** (p. 382), for the class `{w : ‖w‖ ≤ B}`. Let `x₁, …, x_m` be vectors in a real
inner product space and `H₂ ∘ S = {(⟨w, x₁⟩, …, ⟨w, x_m⟩) : ‖w‖ ≤ B}`. Then
`R(H₂ ∘ S) ≤ B · maxᵢ ‖xᵢ‖ / √m`. The book states the case `B = 1`; `B ≥ 0` is assumed. -/
theorem rademacher_linearEvalSet_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (B : ℝ) (hB : 0 ≤ B) (x : Fin m → E) :
    rademacher (linearEvalSet B x) ≤ B * (⨆ i, ‖x i‖) / Real.sqrt m := by sorry

end UnderstandingML
