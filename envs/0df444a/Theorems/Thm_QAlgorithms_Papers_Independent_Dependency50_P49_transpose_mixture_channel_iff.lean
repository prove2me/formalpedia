-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P49_transpose_mixture_channel_iff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P49.transpose_mixture_channel_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:21:17.327711+00:00
-- url     : https://prove2.me/theorems/2068c87e-877e-4b10-ac70-df3afe8a740a
-- title:
--   When the transpose–depolarizing mixture is a channel
-- statement:
--   Let $n$ be a positive integer, $0\leq p\leq1$ a real number, $\Theta(X)=X^{\mathsf T}$ the complex-linear transpose on $\mathcal B(\mathbb C^n)$, and $S(X)=\operatorname{tr}(X)I/n$ the maximally mixed depolarizing channel in the Heisenberg picture. Put $T_p=(1-p)S+p\Theta$. Then
--
--   $$T_p\text{ is completely positive and unital}\quad\Longleftrightarrow\quad n=1\ \text{or}\ p\leq\frac1{n+1}.$$
--
--   Thus in dimension at least two the criterion is exactly the printed one. In dimension one both maps are the identity and every allowed $p$ works. This characterizes the channel used in the norm-separation example.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, PDF p. 13, Proposition 5, Eq. (48), with dimension-one correction

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

namespace QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- The accepted all-Schatten norms at p=top are exactly the source's operator norms.

local notation "inducedNorm" => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm (⊤ : ℝ≥0∞)

local notation "cbNorm" => QAlgorithms.Papers.Independent.Information100.P50.cbNorm (⊤ : ℝ≥0∞)

/-- PDF pp.13–14, Proposition 5, (48): dimension-one correction disclosed.
The printed iff p<=1/(n+1) presupposes a nonzero antisymmetric subspace.
For n=1 both transpose and S are identity, so every p in [0,1] is allowed. -/
theorem transpose_mixture_channel_iff {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsQuantumChannel (transposeMixture n p) ↔ n = 1 ∨ p ≤ 1 / ((n : ℝ) + 1) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P49

end
