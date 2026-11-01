-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P05_one_shot_feinstein
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P05.one_shot_feinstein
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:58:08.572631+00:00
-- url     : https://prove2.me/theorems/d3762c97-bbc6-46a0-a9c0-e1ab8a1088fc
-- title:
--   One-shot quantum Feinstein packing bounds
-- statement:
--   Let $x\mapsto\rho_x$ be a density-output channel on a finite alphabet and finite-dimensional complex Hilbert space. For an input law $p$, put $\sigma=\sum_xp(x)\rho_x$ and $\bar\rho_x=\mathcal E_\sigma(\rho_x)$. Suppose $\delta\ge0$, $c>0$, and
--
--   $$\sum_xp(x)\operatorname{Tr}[\bar\rho_x\{\bar\rho_x-c\sigma>0\}]\ge1-\delta.$$
--
--   For every $\gamma>0$ and $\eta>0$ there are $M\ge1$ distinct words $u_1,\ldots,u_M\in\mathcal X$ and positive decoder operators $X_k$ with $\sum_kX_k\le I$ such that
--
--   $$\frac{\gamma}{\gamma+\delta}\min\{\eta,1-\delta-\gamma-2\sqrt\eta\}\le\frac{M}{c},\qquad \frac1M\sum_{k=1}^M(1-\operatorname{Tr}[\rho_{u_k}X_k])\le\delta+\gamma+2\sqrt\eta.$$
--
--   The test in the premise is the strict positive spectral projection. The error uses the original channel states and uniform messages. This one-shot statement gives both size and reliability of a single code; no upper restriction on $\delta$ or $\eta$ is imposed.
-- source:
--   A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory, arXiv:quant-ph/0208139v1, PDF p. 4, Lemma 2, (17)–(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P05

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr pinch typeI accept)

open QAlgorithms.Papers.Independent.Claimed50.P45 (pinchedTest)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Dependency50.P35 (directSum)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X I : Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

/-- PDF p.4, Lemma 2, (17)–(19): a one-shot quantum Feinstein code with BOTH
cardinality and average-error bounds. There is no delta < 1 hypothesis.
The hypothesis uses pinched states; the output error uses original states. -/
theorem one_shot_feinstein (W : DensityOutputChannel X I) (p : Distribution X)
    (delta c : ℝ) (hdelta : 0 ≤ delta) (hc : 0 < c)
    (hgood : 1 - delta ≤ goodMass W p c)
    (gamma eta : ℝ) (hgamma : 0 < gamma) (heta : 0 < eta) :
    ∃ C : DistinctWordCode X I,
      gamma / (gamma + delta) * min eta (1 - delta - gamma - 2 * Real.sqrt eta) ≤
        (C.size : ℝ) / c ∧
      uniformMessageError W.state C ≤ delta + gamma + 2 * Real.sqrt eta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P05

end
