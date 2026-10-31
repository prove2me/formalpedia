-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_bipartite_self_inverse_cluster
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.bipartite_self_inverse_cluster
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:49:37.295697+00:00
-- url     : https://prove2.me/theorems/8cca2047-971c-4c47-a7be-5fbfbd70a233
-- title:
--   IV.D: bipartite self-inverse H-graph maps to the same ideal graph
-- statement:
--   Let $G=\begin{psmallmatrix}0&G_0^T\\G_0&0\end{psmallmatrix}$ be real with $G^2=I$, where $G_0$ is initially rectangular with $p$ rows and $n$ columns. Then $n=p$ and $G_0^TG_0=G_0G_0^T=I$. For every $\alpha>0$, Fourier transforming one part of the H-graph state gives
--
--   $$Z'=i\operatorname{sech}2\alpha I+\tanh2\alpha G,\qquad E(Z')=n\operatorname{sech}2\alpha.$$
--
--   The output is valid, tends to $G$ as $\alpha\to+\infty$, and its error tends to zero. The empty graph is allowed. No general optimality claim is added.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 15, IV.D: bipartite self-inverse H-graph maps to the same ideal graph

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.15, (4.15)–(4.17): a bipartite self-inverse graph has
balanced parts and orthogonal cross-block; a Fourier transform on one part
gives the same ideal graph and exact finite scalar error. -/
theorem bipartite_self_inverse_cluster (n p : ℕ) (G0 : Matrix (Fin p) (Fin n) ℝ)
    (hInv : (Matrix.fromBlocks 0 G0.transpose G0 0) *
      (Matrix.fromBlocks 0 G0.transpose G0 0) = (1 : Matrix (Fin n ⊕ Fin p) (Fin n ⊕ Fin p) ℝ)) :
    let G : Matrix (Fin n ⊕ Fin p) (Fin n ⊕ Fin p) ℝ := Matrix.fromBlocks 0 G0.transpose G0 0
    n = p ∧ G0.transpose * G0 = 1 ∧ G0 * G0.transpose = 1 ∧
    (∀ alpha : ℝ, 0 < alpha →
      graphLocalMobius 0 (-1) 1 0 (hGraph G alpha) = sechGraph G alpha ∧
      graphError (sechGraph G alpha) = (n : ℝ) * (Real.cosh (2*alpha))⁻¹ ∧
      ValidGraph (sechGraph G alpha)) ∧
    Tendsto (fun alpha => graphLocalMobius 0 (-1) 1 0 (hGraph G alpha)) atTop (nhds (complexify G)) ∧
    Tendsto (fun alpha => graphError (sechGraph G alpha)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
