-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_irreducible_convex_decomposition
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.irreducible_convex_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:44:17.004439+00:00
-- url     : https://prove2.me/theorems/234dd080-e43a-49e3-b244-d5fb0ae3ffe5
-- title:
--   Finite convex decomposition through actual irreducible carriers
-- statement:
--   Let $d\ge1$, $N\ge1$, $M>N$ and $K=\operatorname{Sym}^N\mathbb C^d$. Every CP unital complex-linear cloning map $T:B((\mathbb C^d)^{\otimes M})\to B(K)$ that is covariant under $U(d)$ and invariant under output permutations has a finite decomposition
--   $$
--   T(A)=\sum_{i=1}^r w_i V_i^*\bigl((j_i^*Aj_i)\otimes I_{H_{\beta_i}}\bigr)V_i,\qquad w_i\ge0,\quad\sum_iw_i=1.
--   $$
--   For each $i$, $\pi_{\alpha_i}$ and $\pi_{\beta_i}$ are actual nonzero finite-dimensional irreducible smooth unitary $U(d)$ representations; $j_i:H_{\alpha_i}\hookrightarrow(\mathbb C^d)^{\otimes M}$ is an isometric intertwining inclusion; and $V_i:K\hookrightarrow H_{\alpha_i}\otimes H_{\beta_i}$ is an isometry satisfying
--   $$
--   V_i\pi_N^+(u)=(\pi_{\alpha_i}(u)\otimes\pi_{\beta_i}(u))V_i.
--   $$
--   Here $A$ ranges over arbitrary full-output observables, so its compression $j_i^*Aj_i$ is essential. The decomposition and intertwiners are not claimed unique, and individual embedded block maps need not be permutation invariant. This reduces covariant optimization to irreducible blocks.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 6, Proposition 5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF p.6 Proposition 5: finite convex decomposition through ACTUAL
irreducible carriers, with full-output compression included. No uniqueness
or individual embedded-block permutation invariance is asserted. -/
theorem irreducible_convex_decomposition (d N M : ℕ) (hd : 0 < d)
    (hN : 1 ≤ N) (hNM : N < M) (T : CloneFunction d N M)
    (hT : IsCloning T) (hcov : IsCloningCovariant T) (hperm : IsPermutationInvariant T) :
    ∃ r : ℕ, ∃ w : Fin r → ℝ, ∃ B : Fin r → CloningBlock d N M,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ A, T A = ∑ i, (w i : ℂ) • blockApply (B i) A := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
