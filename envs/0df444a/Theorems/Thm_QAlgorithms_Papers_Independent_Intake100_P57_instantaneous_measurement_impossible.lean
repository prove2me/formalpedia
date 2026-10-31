-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P57_instantaneous_measurement_impossible
-- name    : QAlgorithms.Papers.Independent.Intake100.P57.instantaneous_measurement_impossible
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:00:23.997695+00:00
-- url     : https://prove2.me/theorems/6f77935d-f2f3-49fd-a881-aa2a6bcd3098
-- title:
--   A measurement requiring large shared-entanglement dimension
-- statement:
--   Let $d\ge1$ be a prime power, and let $U_a$, $a=0,\ldots,d$, be unitaries whose columns form $d+1$ pairwise mutually unbiased bases of $\mathbb C^d$. On $A\otimes B=\mathbb C^{d+1}\otimes\mathbb C^d$ define the POVM with effects
--
--   $$
--   O_x=\sum_{a=0}^d|a\rangle\langle a|\otimes U_a|x\rangle\langle x|U_a^\dagger,
--   \qquad x=1,\ldots,d.
--   $$
--
--   Let $M$ be any instantaneous measurement implemented by fixed local POVMs and classical postprocessing of their outcomes, using an arbitrary normalized resource $\eta_{A'B'}$ of finite nonzero local dimensions. Regard both POVMs as their classical-output channels $\rho\mapsto\sum_x\operatorname{Tr}(M_x\rho)|x\rangle\langle x|$. For every real $\epsilon$ such that $\dim B'\le\epsilon\sqrt d$,
--
--   $$
--   \|M-O\|_\diamond\ge2(1-2\epsilon).
--   $$
--
--   The norm is the full diamond norm. The estimate need not be positive when $\epsilon\ge1/2$; that range is not excluded.
--
--   **Formalization Note** The printed (13) is a Kraus operator. The displayed effects are its adjoint times itself; the printed Alice dimension $d$ is replaced by $d+1$ to match the actual construction.
-- source:
--   Simplified instantaneous non-local quantum computation with applications to position-based cryptography, arXiv:1101.1065v3, PDF p. 12, IV.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P57

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P57

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- P34 uses half the channel distance. Every occurrence below is multiplied by two.

open QAlgorithms.Papers.Independent.Information100.P34 (diamondDistance)

open QAlgorithms.Papers.Independent.Dependency50.P07 (ensembleMean)

/-- Corollary IV.2, PDF p.12, with the probability effects of (13), p.11,
corrected as documented in mubEffect. No additional epsilon<1/2 hypothesis:
the lower bound may be uninformative. Alice has d+1 basis-label states. -/
theorem instantaneous_measurement_impossible (d l r : ℕ) (hd : 0 < d)
    (hprime : ∃ p k : ℕ, Nat.Prime p ∧ d = p^k) (hl : 0 < l) (hr : 0 < r)
    (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ) (hU : IsMUB d U)
    (eta : Matrix (Fin l × Fin r) (Fin l × Fin r) ℂ) (heta : IsDensityMatrix eta)
    (s : InstantMeasurement (d+1) d l r d) (epsilon : ℝ)
    (hsize : (r : ℝ) ≤ epsilon * Real.sqrt (d : ℝ)) :
    2 * (1 - 2*epsilon) ≤ 2 * diamondDistance
      (fun X => Matrix.diagonal fun x => (instantEffect s eta x * X).trace)
      (fun X => Matrix.diagonal fun x => (mubEffect U x * X).trace) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P57

end
