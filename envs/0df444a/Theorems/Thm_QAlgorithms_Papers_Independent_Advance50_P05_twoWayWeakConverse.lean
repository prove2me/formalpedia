-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P05_twoWayWeakConverse
-- name    : QAlgorithms.Papers.Independent.Advance50.P05.twoWayWeakConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:26:31.693848+00:00
-- url     : https://prove2.me/theorems/1f8db04a-140b-4751-97fa-96e5c8169d52
-- title:
--   Two-way weak converse with effect smoothing
-- statement:
--   Let $\rho^{AB}$ be a normalized bipartite state on positive-dimensional finite Hilbert spaces, and let $\varepsilon\ge0$. Let $E_D^{\leftrightarrow}(\rho;\varepsilon)$ optimize the log-rank of a positive integer maximally entangled target under actual two-way LOCC with unconditional root fidelity at least $1-\varepsilon$. For a normalized state $r^{CD}$, write
--   $$
--   \widetilde I_{0,\delta}^{C\to D}(r)=\max_{\substack{0\le P\le1\\\operatorname{Tr}(Pr)\ge1-\delta}}\min_{\omega_D\text{ state}}-\log_2\operatorname{Tr}[\sqrt P\,\Pi_r\sqrt P(1_C\otimes\omega_D)],
--   $$
--   where $\Pi_r$ is the support projector and zero overlap gives $+\infty$. Then
--   $$
--   E_D^{\leftrightarrow}(\rho;\varepsilon)\le\max_{\Lambda^{\leftrightarrow}:AB\to A'B'}\widetilde I_{0,2\varepsilon}^{A'\to B'}(\Lambda^{\leftrightarrow}(\rho)).
--   $$
--   The output is computed from the input and an actual adaptive two-way LOCC map. Its positive finite local dimensions may vary in the optimization. The maximum has a map witness whose score bounds all competing map scores, together with attained effect and comparison-state extrema. For $\varepsilon<1$ the operational optimum has a distillation-code witness; for $\varepsilon\ge1$ it is the extended value $+\infty$.
--
--   This is the general two-way converse, with smoothing parameter $2\varepsilon$. **Formalization Note:** LOCC follows the plan's arbitrary finite adaptive-protocol interpretation. The unbounded endpoint does not assert a finite maximizing achievable rate.
-- source:
--   Distilling entanglement from arbitrary resources, arXiv:1006.1896v2, PDF p. 11, Lemma 5, Eq.(38): two-way weak converse

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

/-- Buscemi--Datta, arXiv:1006.1896v2, PDF p.11, Lemma 5, (38).
The smoothing parameter is 2*eps. Preprocessing ranges over actual general
two-way LOCC, not single Alice instruments.
Printed: Definition 2 uses a finite achievable-rate maximum for every eps>=0.
Changed: use an extended supremum, retain a code maximum for eps<1, and set
the operational value to +infinity for eps>=1.
Why: when eps>=1 the fidelity threshold is nonpositive and every positive
integer target rank is feasible; the printed finite maximum does not exist. -/
theorem twoWayWeakConverse
    {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (eps < 1 → OneShotAttained .twoWay rho eps) ∧
    (1 ≤ eps → distillableEntanglementOneShot .twoWay rho eps = ⊤) ∧
    ∃ P : TwoWayPreprocessing A B,
      distillableEntanglementOneShot .twoWay rho eps ≤ effectSmoothedZero (P.operation rho) (2 * eps) ∧
      (∀ Q : TwoWayPreprocessing A B,
        effectSmoothedZero (Q.operation rho) (2 * eps) ≤
          effectSmoothedZero (P.operation rho) (2 * eps)) ∧
      EffectExtremaAttained (P.operation rho) (2 * eps) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P05

end
