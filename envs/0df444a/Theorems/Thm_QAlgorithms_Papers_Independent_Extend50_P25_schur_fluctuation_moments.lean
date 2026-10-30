-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_schur_fluctuation_moments
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.schur_fluctuation_moments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:26:24.134736+00:00
-- url     : https://prove2.me/theorems/d2d9fd92-aff4-4d46-9e88-411a2c340198
-- title:
--   Corollary 4.5: Schur–Weyl fluctuation moments
-- statement:
--   Fix $d\ge1$, $j\in\{1,\ldots,d\}$ and an integer $k\ge0$. For $n\ge1$ draw a partition $\alpha^{(n)}$ with mass $d_\alpha m_{d,\alpha}/d^n$ and put $A_j^{(n)}=(\alpha_j^{(n)}-n/d)/\sqrt{n/d}$. Let $A$ be the nonincreasing eigenvalue vector of the trace-centered GUE with diagonal variance 1 and off-diagonal coordinate variance $1/2$. Then the family $\{(A_j^{(n)})^k:n\ge1\}$ is uniformly integrable, $A_j^k$ is integrable, and
--   $$\lim_{n\to\infty}\mathbb E[(A_j^{(n)})^k]=\mathbb E[A_j^k].$$
--   This retains both absolute-tail control and convergence of the possibly signed moments, including the constant-one case $k=0$.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 26, Corollary 4.5: Schur–Weyl fluctuation moments

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Corollary 4.5, PDF p.26: uniform integrability AND convergence of every ordered
Schur–Weyl fluctuation moment. Uniform integrability is expanded as uniform absolute
moment tails, so the finite laws can vary with n. n=0 is excluded, k=0 is allowed. -/
theorem schur_fluctuation_moments (d : ℕ) (hd : 1 ≤ d) (j : Fin d) (k : ℕ) :
    Integrable (fun x => gueSpectrum d x j ^ k) (normalCoordinates (Fin d × Fin d)) ∧
    (∀ eta : ℝ, 0 < eta → ∃ R : ℝ, 0 < R ∧ ∀ n : ℕ, 1 ≤ n →
      (∑ a : SchurDiagram d n,
        if R < |fluctuation a j ^ k| then schurMass a * |fluctuation a j ^ k| else 0) ≤ eta) ∧
    Filter.Tendsto (fun n : ℕ => ∑ a : SchurDiagram d n, schurMass a * fluctuation a j ^ k)
      Filter.atTop (nhds (∫ x, gueSpectrum d x j ^ k ∂normalCoordinates (Fin d × Fin d))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
