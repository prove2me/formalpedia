-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_asymptotic_mixing
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.asymptotic_mixing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:10:50.832987+00:00
-- url     : https://prove2.me/theorems/7eb7d6e2-693e-4d30-a976-407a97172822
-- title:
--   Unnumbered Lemma: asymptotic LOCC mixing
-- statement:
--   Let $\rho,\sigma$ be normalized densities on the same positive finite bipartite local dimensions, and let $0\le p\le1$. Actual asymptotic LOCC achieves
--
--   $$\rho^{\otimes(1-p)}\otimes\sigma^{\otimes p}\longrightarrow(1-p)\rho+p\sigma.$$
--
--   The exponents denote copy supplies, with floors. For each positive error and output-rate slack the conversion works at every sufficiently large block length with unconditional normalized output. Endpoints are included. The slack formulation absorbs the source construction's sublinear copy overhead.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 3, Unnumbered Lemma: asymptotic LOCC mixing

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.3, unnumbered asymptotic mixing Lemma (21).
The output-rate slack absorbs the o(N) typical-window overhead; endpoints
p=0,1 are included. The erroneous binomial weights in (22)–(23) are not asserted. -/
theorem asymptotic_mixing
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho sigma : VidalOperator a b) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    AsymptoticLOCCConverts (single rho (1-p) ++ single sigma p) (single (affineMixture rho sigma p) 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
