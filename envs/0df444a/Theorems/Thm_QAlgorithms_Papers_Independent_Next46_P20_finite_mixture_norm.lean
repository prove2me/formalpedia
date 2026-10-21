-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_finite_mixture_norm
-- name    : QAlgorithms.Papers.Independent.Next46.P20.finite_mixture_norm
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:23:16.7954+00:00
-- url     : https://prove2.me/theorems/cb7d992b-e9ae-4eea-9c5a-a2a7358238dc
-- title:
--   Norm and normalization of a finite orthogonal-window mixture
-- statement:
--   Let $n\ge1$ and let $(\chi_k)_{k=1}^m$ be a finite pairwise orthogonal family in $L^2(\mathbb R^n)$ satisfying $\sum_k\|\chi_k\|^2=1$. For arbitrary $\psi_k\in L^2(\mathbb R^n)$, put $\Psi=\sum_k\psi_k\otimes\overline{\chi_k}$. Then
--   $$
--   \|\Psi\|^2=\sum_k\|\psi_k\|^2\|\chi_k\|^2.
--   $$
--   If every component $\psi_k$ has norm one, then $\|\Psi\|=1$. Zero windows are permitted; the weight condition rules out an empty or entirely zero family.
--
--   This valid norm identity is separate from the defective mixed-state observable formulas later in the section.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 11, §3, unnumbered: norm and normalization of a finite mixture

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.11, §3: the finite orthogonal-window norm identity and normalization.
Zero windows are allowed; there is no division by a window norm. -/
theorem finite_mixture_norm {n m : ℕ} (hn : 0 < n)
    (chi psi : Fin m → ConfigurationL2 n)
    (hOrthogonal : ∀ j k, j ≠ k → inner ℂ (chi j) (chi k) = 0)
    (hWeights : ∑ k, ‖chi k‖ ^ 2 = 1) :
    ‖∑ k, tensorEmbedding (chi k) (psi k)‖ ^ 2 =
      ∑ k, ‖psi k‖ ^ 2 * ‖chi k‖ ^ 2 ∧
    ((∀ k, ‖psi k‖ = 1) → ‖∑ k, tensorEmbedding (chi k) (psi k)‖ = 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
