-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P23_amplitudeDampingViolation
-- name    : QAlgorithms.Papers.Independent.Information100.P23.amplitudeDampingViolation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:13:01.713774+00:00
-- url     : https://prove2.me/theorems/0f82819b-8402-4317-839a-abfa9f770a93
-- title:
--   §5 Consistency: amplitude damping violates the inequality except at the point channel
-- statement:
--   Fix a normalized qubit Bloch basis and $0\le\alpha\le1$. The amplitude-damping channel has affine data $A=\operatorname{diag}(\alpha,\alpha,\alpha^2)$ and $c=(0,0,1-\alpha^2)$; $\alpha$ denotes the coherence multiplier. The explicitly reconstructed complex-linear map is CPTP, and extracting its Bloch data returns precisely this pair. Exactly,
--
--   $$\|A\|_*^2+|c|^2=1+2\alpha^2+4\alpha^3+2\alpha^4.$$
--
--   For $\alpha>0$ this is strictly larger than $1$, and the channel is not entanglement breaking. At $\alpha=0$ it equals $1$, and the map is the EB replacement channel $X\mapsto\operatorname{Tr}(X)\rho(0,0,1)$ with pure output. This gives the exact algebraic content of the source's asymptotic consistency check.
-- source:
--   A sharp norm inequality for entanglement-breaking channels, arXiv:2609.27906v1, PDF p. 4, §5 Consistency: amplitude damping violates the inequality except at the point channel

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P23

/-- PDF p.4, §5, Consistency: exact expansion of the displayed asymptotic formula.
Alpha is in [0,1]; zero is the EB pure-output point channel, all positive alpha fail the bound. -/
theorem amplitudeDampingViolation (B : BlochBasis 2) (alpha : ℝ)
    (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1) :
    let Phi := amplitudeDamping B alpha
    IsCPTP Phi ∧
    blochA B Phi = Matrix.diagonal ![alpha, alpha, alpha ^ 2] ∧
    blochC B Phi = ![0, 0, 1 - alpha ^ 2] ∧
    nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 =
      1 + 2 * alpha ^ 2 + 4 * alpha ^ 3 + 2 * alpha ^ 4 ∧
    (0 < alpha → 1 < nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 ∧
      ¬ Entanglement.IsEntanglementBreakingPositive Phi) ∧
    (alpha = 0 → Entanglement.IsEntanglementBreakingPositive Phi ∧
      nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 = 1 ∧
      ∀ X : Operator 2, Phi X = X.trace • blochState B ![0, 0, 1]) := by sorry

end QAlgorithms.Papers.Independent.Information100.P23

end
