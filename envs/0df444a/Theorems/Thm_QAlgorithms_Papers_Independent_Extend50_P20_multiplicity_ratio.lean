-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_multiplicity_ratio
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.multiplicity_ratio
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:08:07.805029+00:00
-- url     : https://prove2.me/theorems/edf2f864-da58-4697-b24f-621713cdd928
-- title:
--   Ratio of squared physical Schur multiplicities
-- statement:
--   Let $d\ge1$ and $1\le k<N$. Write $S_r=\sum_{\lambda\vdash r,\,h(\lambda)\le d}m_\lambda^2$, where $m_\lambda$ is the actual multiplicity of the irreducible $S_r$ representation labelled by $\lambda$ in the tensor-factor permutation action on $(\mathbb C^d)^{\otimes r}$. Then
--
--   $$\frac{S_N}{S_{N-k}}=\prod_{j=0}^{k-1}\frac{d^2+N-1-j}{N-j}.$$
--
--   Every denominator is positive on this domain. This relates physical multiplicity sums at different tensor degrees. **Formalization Note** Multiplicities are dimensions of constructed Schur modules, rather than arbitrary numbers satisfying the identity.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 14, Theorem 9 / Eq. (46)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Theorem 9, PDF p.14, Eq.(46); Appendix D pp.22-23.
Use the explicitly proved range 1 <= k <= N-1 and exactly k telescoping
factors. The appendix's final reference to Theorem 3 and extra factor are typos. -/
theorem multiplicity_ratio (d N k : ℕ)
    (hd : 0 < d) (hk : 1 ≤ k) (hkN : k < N) :
    multiplicitySquares d N / multiplicitySquares d (N-k) =
      ∏ j ∈ Finset.range k, ((d : ℝ)^2+(N : ℝ)-1-(j : ℝ))/((N : ℝ)-(j : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
