-- Prove2me | Theorems.Thm_RegOTQuant_TwiceDiff_lemma_2_3_iii
-- name    : RegOTQuant.TwiceDiff.lemma_2_3_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:05.591983+00:00
-- url     : https://prove2.me/theorems/7c48fc34-491d-4502-831e-1f6c270997e2
-- title:
--   Lemma 2.3(iii), p. 8 — entropy bound for discrete marginals
-- statement:
--   Let $\pi$ couple $N\ge1$ probability measures $\mu_1,\ldots,\mu_N$. For each $i=2,\ldots,N$, suppose $\mu_i$ is supported on at most $n_i\ge1$ points. With $P=\bigotimes_i\mu_i$ and the entropic generator $f(t)=t\log t$,
--
--   $$D_f(\pi,P)\le\sum_{i=2}^N\log n_i.$$
--
--   This is the finite-support relative-entropy bound used for Theorem 3.8(i).
--
--   **Formalization Note** Lean's index $0$ is the paper's first marginal, so the sum omits index $0$. The Lean statement specializes the general Polish spaces of Lemma 2.3 to Euclidean spaces.
-- source:
--   Eckstein & Nutz, Convergence rates for regularized optimal transport via quantization, arXiv:2208.14391v3, p. 8, Lemma 2.3(iii)

import Mathlib
import Definitions.Def_RegOTQuant_TwiceDiff_Setting

open MeasureTheory Set

namespace RegOTQuant.TwiceDiff

/-- Lemma 2.3(iii), p. 8, specialized to Euclidean marginal spaces.
Lean index 0 is the paper's first marginal. -/
theorem lemma_2_3_iii {N : ℕ} {d : Fin N → ℕ}
    (Xs : ∀ i : Fin N, Set (Fi d i)) (μ : ∀ i : Fin N, Measure (Fi d i))
    (π : Measure (E d)) (n : Fin N → ℕ)
    (hN : 0 < N) (hπ : π ∈ couplings μ)
    (hμprob : ∀ i, IsProbabilityMeasure (μ i))
    (hn : ∀ i, i.val ≠ 0 → 1 ≤ n i ∧ IsAtMostN (n i) (Xs i) (μ i)) :
    fDiv (fun x : ℝ => x * Real.log x) π (prodRef μ) ≤
      (((∑ i : Fin N, if i.val = 0 then (0 : ℝ)
        else Real.log (n i : ℝ)) : ℝ) : EReal) := by sorry

end RegOTQuant.TwiceDiff
