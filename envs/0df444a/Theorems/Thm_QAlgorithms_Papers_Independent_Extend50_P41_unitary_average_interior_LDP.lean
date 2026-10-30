-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_unitary_average_interior_LDP
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.unitary_average_interior_LDP
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:48:28.363091+00:00
-- url     : https://prove2.me/theorems/b681573c-f48f-4a8d-83a2-92b0bf8a8fc2
-- title:
--   Proposition 4.8: unitary averaging gives the worst orbit rate on full-rank inputs
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   A scheme with rate $I$ satisfies the closed-set upper and open-set lower large-deviation bounds for every input; $I(\rho,\cdot)$ is good and vanishes exactly at the target of $\rho$.
--
--   For a full scheme with rate $I$, let
--   $$\overline E_N(B)=\int_{U(d)}U^{\otimes N}E_N(U^*BU)(U^*)^{\otimes N}\,dU,$$
--   where Haar measure has mass one. This is a normalized covariant scheme. For every positive-definite input $\rho$, its Born laws satisfy the LDP with
--   $$\overline I_\rho(\sigma)=\inf_{U\in U(d)}I(U^*\rho U,U^*\sigma U).$$
--   The assertion is only for such inputs and makes no full boundary-input LDP claim. It identifies the exponent after unitary averaging.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 17, Proposition 4.8 / (81),(82)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.17-18, Proposition 4.8, (82): the averaged laws have the orbit
infimum rate at positive-definite inputs. No boundary-input LDP is claimed. -/
theorem unitary_average_interior_LDP {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (hI : SchemeLDP E FullTarget I) :
    ∃ A : Scheme d (DensityOutcome d),
      (∀ k B, MeasurableSet B → (A.observable k).operator B = unitaryAverageOperator E k B) ∧
      (∀ k, CovariantAt (A.observable k)) ∧
      ∀ rho, rho.val.PosDef → HasLDP (fun k => A.law k rho) (orbitRate I rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
