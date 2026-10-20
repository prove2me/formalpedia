-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_forwardPublicInvariance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.forwardPublicInvariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:38:55.334431+00:00
-- url     : https://prove2.me/theorems/cce20ca3-19e6-4e63-a967-567af023e5e5
-- title:
--   Forward public communication does not improve private or key capacities
-- statement:
--   Let $W:x\mapsto\rho_x^{QE}$ be a normalized finite classical–quantum wiretap channel, and let $\mathcal N$ be a finite-dimensional quantum channel with a fixed isometric dilation $U:P\to Q\otimes E$. All alphabets and registers are nonempty. Bob receives $Q$, and Eve receives all of $E$. Use the operational uniform-message and uniform-key models with separate reliability, public-leakage, and conditional Eve-leakage constraints, and arbitrary mixed block inputs for $\mathcal N$. Write $\to$ for free forward public communication from Alice to Bob, visible to Eve; there is no backward communication or initially shared resource. Then
--
--   $$C_p^{\to}(W)=C_p(W),\qquad K^{\to}(W)=K(W),$$
--   $$C_p^{\to}(\mathcal N)=C_p(\mathcal N),\qquad K^{\to}(\mathcal N)=K(\mathcal N).$$
--
--   Rates use base-two logarithms and positive blocklengths. The result shows that the public transcript can be dispensed with without changing either asymptotic capacity.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 5, Direct coding theorem, unnumbered conclusion

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Unnumbered direct-coding conclusion, PDF p.5, transferred to quantum
channels on p.9: free forward public communication improves neither capacity.
Eve sees the transcript. There is no backward channel or initial shared resource. -/
theorem forwardPublicInvariance [Nonempty X] [Nonempty P] [Nonempty Q] [Nonempty E]
    (W : X → Matrix (Q × E) (Q × E) ℂ) (hW : ∀ x, IsDensityMatrix (W x))
    (U : Matrix (Q × E) P ℂ) (hU : IsDilation U) :
    cqCapacity W .message true = cqCapacity W .message false ∧
    cqCapacity W .key true = cqCapacity W .key false ∧
    quantumPrivateCapacity U .message true = quantumPrivateCapacity U .message false ∧
    quantumPrivateCapacity U .key true = quantumPrivateCapacity U .key false := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
