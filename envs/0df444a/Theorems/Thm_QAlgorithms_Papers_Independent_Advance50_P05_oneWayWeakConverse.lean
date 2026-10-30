-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P05_oneWayWeakConverse
-- name    : QAlgorithms.Papers.Independent.Advance50.P05.oneWayWeakConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:25:23.901241+00:00
-- url     : https://prove2.me/theorems/9d92a188-205d-4fc4-b021-4022ca56b3d5
-- title:
--   One-way weak converse with effect smoothing
-- statement:
--   Let $\rho^{AB}$ be a normalized bipartite state on positive-dimensional finite Hilbert spaces, and let $\varepsilon\ge0$. Let $E_D^{\to}(\rho;\varepsilon)$ be the optimal log-rank obtainable by forward LOCC at unconditional root fidelity at least $1-\varepsilon$. For $\delta\ge0$, define
--   $$
--   p(r;\delta)=\{P:0\le P\le1,\ \operatorname{Tr}(Pr)\ge1-\delta\},\qquad
--   \widetilde I_{0,\delta}^{C\to D}(r)=\max_{P\in p(r;\delta)}\min_{\omega_D\text{ state}}-\log_2\operatorname{Tr}[\sqrt P\,\Pi_r\sqrt P(1_C\otimes\omega_D)],
--   $$
--   where $\Pi_r$ is the support projector and zero overlap gives $+\infty$. For an instrument $\mathcal I_A=\{\mathcal E_x:A\to A'\}$, set $\sigma_{\mathcal I}=\sum_x(\mathcal E_x\otimes\mathrm{id}_B)(\rho)\otimes|x\rangle\langle x|$, with all outcomes retained and $X$ held by Bob. Then
--   $$
--   E_D^{\to}(\rho;\varepsilon)\le\max_{\mathcal I_A}\widetilde I_{0,4\sqrt\varepsilon}^{A'\to BX}(\sigma_{\mathcal I}).
--   $$
--   The maximum is represented by an instrument witness whose score bounds every other instrument score; its effect and normalized comparison-state extrema are attained. For $\varepsilon<1$ the operational log-rank optimum also has a physical code witness. For $\varepsilon\ge1$, achievable finite rates are unbounded and the operational value is $+\infty$; the effect-smoothed upper bound is likewise $+\infty$.
--
--   This bound reduces forward preprocessing to Alice's instrument. **Formalization Note:** the endpoint uses extended values, since the printed operational finite maximum does not exist there. No finite maximizing achievable rate is claimed at that endpoint.
-- source:
--   Distilling entanglement from arbitrary resources, arXiv:1006.1896v2, PDF p. 9, Lemma 4 (One-way weak converse), Eq.(31)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P05

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P19 (first both epr IsIso)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Support50.P21 (dMin weakPositive PositiveTensorBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Buscemi--Datta, arXiv:1006.1896v2, PDF pp.9--11, Lemma 4, (31).
The parameter is 4*sqrt(eps), with Bob-side flags. Preserve the maximum
and its effect/comparison witnesses.
Printed: Definition 2 uses a finite achievable-rate maximum for every eps>=0.
Changed: use an extended supremum, retain a code maximum for eps<1, and set
the operational value to +infinity for eps>=1.
Why: when eps>=1 the fidelity threshold is nonpositive and every positive
integer target rank is feasible; the printed finite maximum does not exist. -/
theorem oneWayWeakConverse
    {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (eps < 1 → OneShotAttained .forward rho eps) ∧
    (1 ≤ eps → distillableEntanglementOneShot .forward rho eps = ⊤) ∧
    ∃ P : AlicePreprocessing A,
      distillableEntanglementOneShot .forward rho eps ≤ effectSmoothedZero (P.output rho) (4 * Real.sqrt eps) ∧
      (∀ Q : AlicePreprocessing A,
        effectSmoothedZero (Q.output rho) (4 * Real.sqrt eps) ≤
          effectSmoothedZero (P.output rho) (4 * Real.sqrt eps)) ∧
      EffectExtremaAttained (P.output rho) (4 * Real.sqrt eps) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P05

end
