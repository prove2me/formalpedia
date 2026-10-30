-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P45_finiteCQContinuity_sharp
-- name    : QAlgorithms.Papers.Independent.Advance50.P45.finiteCQContinuity_sharp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:18:41.118039+00:00
-- url     : https://prove2.me/theorems/9955c2aa-951e-4de1-a63a-467d2e1d44af
-- title:
--   Sharp continuity of finite classical–quantum conditional entropy
-- statement:
--   Let $B$ be a nonzero finite-dimensional quantum system of dimension $d_B$, and let $0<\varepsilon\le 1-1/d_B$. For any finite alphabet $\mathcal X$, consider normalized states classical in the same orthonormal basis of $X$,
--   $$
--   \rho_{XB}=\sum_x r(x)|x\rangle\langle x|\otimes\rho_B^x,
--   \qquad
--   \sigma_{XB}=\sum_x s(x)|x\rangle\langle x|\otimes\sigma_B^x.
--   $$
--   Here $r,s$ are arbitrary probability distributions and every branch operator is positive semidefinite with trace one, including at labels of zero probability. Define $H(B|X)_\rho=\sum_x r(x)H(\rho_B^x)$ and analogously for $\sigma$, where $H$ is the von Neumann entropy in bits. If $\frac12\|\rho_{XB}-\sigma_{XB}\|_1\le\varepsilon$, with $\|\cdot\|_1$ the Schatten trace norm, then
--   $$
--   \bigl|H(B|X)_\rho-H(B|X)_\sigma\bigr|
--   \le \varepsilon\log_2(d_B-1)+h_2(\varepsilon),
--   \qquad
--   h_2(t)=-t\log_2t-(1-t)\log_2(1-t),
--   $$
--   with $0\log_2 0=0$. Moreover, for every allowed $d_B$ and $\varepsilon$, there is a pair satisfying the distance bound for which equality holds; a singleton classical alphabet suffices.
--
--   Thus the dimension- and distance-dependent bound cannot be improved uniformly over CQ states.
-- source:
--   Optimal uniform continuity bound for conditional entropy of classical--quantum states, arXiv:1909.01755v2, PDF p. 2, Proposition 1, Eqs. (4)–(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P45

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (cqBlock)

/-- Proposition 1, PDF p.2, Eqs.(4)–(6), proof pp.3–4: the uniform finite
CQ continuity bound AND its sharpness at every allowed dimension/error.
The universal pair is unrestricted apart from normalization, common classical
basis and the distance bound. The sharpness pair can use a singleton alphabet.
No entropy ordering or dephasing property from the proof is assumed. -/
theorem finiteCQContinuity_sharp {B : Type*} [Fintype B] [Nonempty B]
    [DecidableEq B] (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hupper : epsilon ≤ 1 - 1 / (Fintype.card B : ℝ)) :
    (∀ (X : Type*) [Fintype X] (R S : CQState X B),
      finiteCQDistance R S ≤ epsilon →
        |cqConditionalEntropy R - cqConditionalEntropy S| ≤
          epsilon * Real.logb 2 ((Fintype.card B : ℝ) - 1) + binEntropy2 epsilon) ∧
    (∃ R S : CQState Unit B, finiteCQDistance R S ≤ epsilon ∧
      |cqConditionalEntropy R - cqConditionalEntropy S| =
        epsilon * Real.logb 2 ((Fintype.card B : ℝ) - 1) + binEntropy2 epsilon) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P45

end
