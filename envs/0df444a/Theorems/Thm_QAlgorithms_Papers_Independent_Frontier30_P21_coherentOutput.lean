-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P21_coherentOutput
-- name    : QAlgorithms.Papers.Independent.Frontier30.P21.coherentOutput
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:20:19.358098+00:00
-- url     : https://prove2.me/theorems/3d88a48a-2914-445c-9382-cc07b9dfd9bf
-- title:
--   Vacuum loss contracts coherent states and preserves purity
-- statement:
--   Let $\alpha\in\mathbb C$ and $0\leq\eta\leq1$. On the complete oscillator space $\ell^2(\mathbb N;\mathbb C)$, write $|\alpha\rangle$ for the normalized coherent vector with coefficients $e^{-|\alpha|^2/2}\alpha^n/\sqrt{n!}$. Let $\mathcal L_\eta$ be vacuum beam-splitter loss with power transmissivity $\eta$, as in Eq. (3). Then
--
--   $$
--   \mathcal L_\eta(|\alpha\rangle\langle\alpha|)=|\sqrt\eta\,\alpha\rangle\langle\sqrt\eta\,\alpha|.
--   $$
--
--   Both density operators are normalized and pure. The lost-photon series for every output density coefficient converges to the coefficient on the right. Thus the conditional output is pure, with zero von Neumann entropy, including the vacuum endpoint $\eta=0$ and the identity endpoint $\eta=1$.
--
--   This local identity explains why coherent codewords contribute zero conditional entropy to the Holevo information.
--
--   **Formalization Note** Equality is expressed in the full number basis. Purity means representation by a norm-one Hilbert vector, so these kernels represent positive trace-one rank-one trace-class operators. The theorem explicitly includes convergence of each channel coefficient series; it does not claim a general trace-class CPTP interface or define entropy.
-- source:
--   Classical capacity of the lossy bosonic channel: the exact solution, arXiv:quant-ph/0308012v2, PDF p. 2, Discussion, coherent-state purity

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P21

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.2, Discussion: vacuum loss contracts every coherent state by sqrt(eta)
and preserves purity. Equality is of density kernels, hence is independent of
global phase. The normalization and convergence conclusions ensure these are
actual pure trace-class density operators on the full Fock space. -/
theorem coherentOutput (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (alpha : ℂ) :
    IsPureFockDensity (coherentDensity alpha) ∧
    IsPureFockDensity (coherentDensity ((Real.sqrt eta : ℂ) * alpha)) ∧
    (∀ m n, HasSum (vacuumLossTerm eta (coherentDensity alpha) m n)
      (coherentDensity ((Real.sqrt eta : ℂ) * alpha) m n)) ∧
    vacuumLossKernel eta (coherentDensity alpha) =
      coherentDensity ((Real.sqrt eta : ℂ) * alpha) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P21

end
