-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_memory_extension_score
-- name    : QAlgorithms.Papers.Independent.Information100.P27.memory_extension_score
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:22:24.644142+00:00
-- url     : https://prove2.me/theorems/908571a2-3306-415d-867c-0912a42796ee
-- title:
--   Appendix D.9.1: exact score change under memory extension
-- statement:
--   Let $p$ be a finite probability distribution, let $e_i$ be normalized pure environmental states, and let $\tau_{i,TZ}$ be arbitrary density matrices. Form $\Omega_{Y T Z E}=\sum_i p_i|i\rangle\langle i|\otimes\tau_{i,TZ}\otimes e_i$ and obtain the original memory by the actual partial trace $\tau_{i,T}=\operatorname{Tr}_Z\tau_{i,TZ}$. For every real $\alpha$, the change in the bottleneck objective is
--
--   $$
--   [\alpha I(TZ;E)-I(TZ;Y)]_\Omega-[\alpha I(T;E)-I(T;Y)]_\Omega
--   =\alpha I(Z;E|T)_\Omega-I(Z;Y|T)_\Omega.
--   $$
--
--   Both conditional mutual informations are nonnegative and $I(Z;E|T)_\Omega\le I(Z;Y|T)_\Omega$. In particular, the score change at $\alpha=1$ is nonpositive. No fixed sign is asserted for $\alpha>1$; the extension identity does not establish the memory-reduction conjecture.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 77, Appendix D.9.1: exact score change under memory extension

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF p.77, (D.122)-(D.124): exact score change, both
conditional-information signs, data processing, and the alpha=1 sign. -/
theorem memory_extension_score {Y T Z E : Type}
    [Fintype Y] [Fintype T] [Fintype Z] [Fintype E]
    [Nonempty Y] [Nonempty T] [Nonempty Z] [Nonempty E]
    (p : Y → ℝ) (e : Y → Matrix E E ℂ)
    (tau : Y → Matrix (T × Z) (T × Z) ℂ)
    (hp : IsProbability p) (he : ∀ i, IsDensityMatrix (e i))
    (hpure : IsPureFamily e) (htau : ∀ i, IsDensityMatrix (tau i)) (alpha : ℝ) :
    memoryScore alpha p e tau - memoryScore alpha p e (fun i => traceRight (tau i)) =
      alpha * extensionEnvironmentInformation p e tau - extensionLabelInformation p tau ∧
    0 ≤ extensionEnvironmentInformation p e tau ∧
    0 ≤ extensionLabelInformation p tau ∧
    extensionEnvironmentInformation p e tau ≤ extensionLabelInformation p tau ∧
    memoryScore 1 p e tau ≤ memoryScore 1 p e (fun i => traceRight (tau i)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
