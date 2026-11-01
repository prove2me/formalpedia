-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_perturbedInseparableAvoidsAcceptance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.perturbedInseparableAvoidsAcceptance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:33:09.713313+00:00
-- url     : https://prove2.me/theorems/09c93721-d595-42f5-8569-4cc8a69f8204
-- title:
--   A small positive identity perturbation avoids the finite acceptance test
-- statement:
--   Let $n,m\ge1$ be finite local mode counts, with interleaved quadratures $(X_1,P_1,\ldots)$, $[X_j,P_j]=i$, and doubled covariance $\gamma_{ab}=2\operatorname{Re}\langle(R_a-d_a)(R_b-d_b)\rangle$. Thus vacuum covariance is $I$. Put $J_r=\bigoplus_{j=1}^r\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. A covariance matrix (CM) is real symmetric and satisfies $\gamma-iJ\succeq0$. All inequalities below are Loewner inequalities.
--
--   Let $\gamma_0=\begin{pmatrix}A_0&C_0\\C_0^T&B_0\end{pmatrix}$ be a physical $n|m$ CM. Construct the sequence as follows: a nonphysical matrix is followed by zero; otherwise put $X_j=C_j(B_j-iJ)^+C_j^T$, $A_{j+1}=B_{j+1}=A_j-\operatorname{Re}X_j$, and $C_{j+1}=-\operatorname{Im}X_j$. All inverses are spectral Moore–Penrose inverses. Every positive-index matrix has split $n|n$. Set $L_j=A_j-\|C_j\|_{\mathrm{op}}I$ for $j\ge1$, where the norm is Euclidean induced. Separability always means the trace-norm closed convex hull of full oscillator product densities, independently of covariance witness inequalities.
--
--   If the physical input $\gamma$ is inseparable, there exists $\epsilon>0$ such that, when the iteration is initialized at $\gamma_0=\gamma+\epsilon I$, every integer $N\ge1$ satisfies
--
--   $$
--   N\le\frac{\|A_0\|_{\mathrm{tr}}-2n}{\epsilon}
--   \quad\Longrightarrow\quad L_N\not\succeq iJ.
--   $$
--
--   Here $A_0$ is the first local block of the perturbed input. The cutoff has no $+1$. This is an existential one-way statement about the perturbed initialization.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 3, Corollary 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Topology ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsSeparable IsBarycenter productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

/-- PDF p.3, Corollary 2: existential noise, one-way finite absence test on
the perturbed initialization. The real cutoff has NO +1. -/
theorem perturbedInseparableAvoidsAcceptance {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (g : CovarianceBlocks n m) (hg : IsPhysicalCovariance g) (hsep : ¬ SeparableCM g) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      let g0 : CovarianceBlocks n m :=
        { A := g.A + epsilon • (1 : Cov n)
          B := g.B + epsilon • (1 : Cov m)
          C := g.C }
      ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) ≤
        (QAlgorithms.traceNorm (complexify g0.A) - 2 * (n : ℝ)) / epsilon →
        ¬ Uncertainty (lowerWitness (tail g0 k)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
