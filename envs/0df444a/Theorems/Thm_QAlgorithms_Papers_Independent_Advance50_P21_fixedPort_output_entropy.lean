-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_fixedPort_output_entropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.fixedPort_output_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:00:44.736263+00:00
-- url     : https://prove2.me/theorems/067e4cdc-37e4-4a31-b807-9d2d3744cdbf
-- title:
--   Unnumbered fixed-port output entropy lower bounds (7.4)–(7.6)
-- statement:
--   Let $d\ge2$, $a\in[0,1]$, and let $\sigma$ be a normalized $d$-dimensional state. Define the fixed-port channel $\mathcal E_{a,\sigma}(X)=\operatorname{Tr}_2(U_a(X\otimes\sigma)U_a^\dagger)$, where $U_a=\sqrt a\,I+i\sqrt{1-a}\,S$ and $S$ swaps the two factors. Write $s=H(\sigma)$, $c_E=(\log d)^{-2}$, $c_N=(d-1)^{-1}$, and define
--   $$\begin{aligned}G_0(t)&=at+(1-a)s,\\G_1(t)&=c_E^{-1}\log\bigl(ae^{c_Et}+(1-a)e^{c_Es}\bigr),\\G_2(t)&=c_N^{-1}g\bigl(a g^{-1}(c_Nt)+(1-a)g^{-1}(c_Ns)\bigr).\end{aligned}$$
--   Here $H(\rho)=-\operatorname{Tr}(\rho\log\rho)$ is the von Neumann entropy in nats, with zero-weight terms defined by continuity. Write $g(x)=(x+1)\log(x+1)-x\log x$ for $x\ge0$, and let $g^{-1}$ be its inverse from nonnegative entropies to nonnegative occupations.
--   For every normalized input state $\rho$ and each $j\in\{0,1,2\}$,
--   $$H(\mathcal E_{a,\sigma}(\rho))\ge G_j(H(\rho)).$$
--   These are all three output-entropy lower bounds (7.4)–(7.6).
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 26, Unnumbered fixed-port output entropy lower bounds (7.4)–(7.6)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.26, (7.4)–(7.6): all three fixed-port output-entropy lower bounds. -/
theorem fixedPort_output_entropy {d : ℕ} (hd : 2 ≤ d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j : Fin 3, outputBound d a (entropy sigma) j (entropy rho) ≤
      entropy (fixedPort a sigma rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
