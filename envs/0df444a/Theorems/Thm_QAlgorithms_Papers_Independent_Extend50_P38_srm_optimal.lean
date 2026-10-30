-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_srm_optimal
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.srm_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:53:21.276515+00:00
-- url     : https://prove2.me/theorems/8d42149d-3716-42a2-9b91-07377605aa27
-- title:
--   Optimality of qubit SRM for a fixed singlet resource
-- statement:
--   For any $N\geq1$, fix the shared resource to be $N$ spin singlets. Let $\sigma_i=2^{-(N-1)}P^-_{BA_i}\otimes I_{\bar A_i}$, $\rho=\sum_i\sigma_i$, and
--
--   $$\Pi_i^{\rm SQ}=\rho^{-1/2}\sigma_i\rho^{-1/2}+\Delta,\qquad\Delta=\frac1N\left(I-\sum_i\rho^{-1/2}\sigma_i\rho^{-1/2}\right).$$
--
--   These effects form a POVM, $\operatorname{Tr}(\sigma_i\Delta)=0$ for every port, and for every other $N$-outcome POVM $\{M_i\}$ on Alice's ports and input,
--
--   $$F(\Lambda_M)\leq F(\Lambda_{\rm SQ}).$$
--
--   Here $\Lambda_M$ denotes the physical protocol with the fixed singlet resource, and $F$ is its maximally-entangled-input entanglement fidelity. Thus SRM attains the best fidelity over Alice's measurements for that resource.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 3, Optimality assertion p.2 and proof pp.3–4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF pp.2–4: SRM is optimal among all N-outcome measurements for the fixed
resource of N singlets. General-d optimality is not asserted. -/
theorem srm_optimal (N : ℕ) (hN : 0 < N) :
    IsPOVM (srm (singletSignals N)) ∧
    (∀ i, (singletSignals N i * srmCompletion (singletSignals N)).trace = 0) ∧
    ∀ M : Fin N → Matrix (AC 2 N) (AC 2 N) ℂ, IsPOVM M →
      QuditFidelity.entanglementFidelity 2 (by decide) (processor M (singletResource N)) ≤
        QuditFidelity.entanglementFidelity 2 (by decide) (singletSrmChannel N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
