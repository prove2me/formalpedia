-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_bsstCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.bsstCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:17:55.9662+00:00
-- url     : https://prove2.me/theorems/f32955c1-0e9f-46a0-acb7-3366327efa9f
-- title:
--   BSST capacity as an attained mutual-information maximum
-- statement:
--   Let $A$ and $A'$ be nonzero finite-dimensional Hilbert spaces and let $\Phi:A\to A'$ be a completely positive trace-preserving channel. All logarithms and entropies are in bits. For each block length $n\ge1$, let $C_{\rm ea}^{(1)}(\Phi^{\otimes n})$ be the maximum output Holevo information over finite message distributions, one normalized pure resource shared with a reference of dimension $(\dim A)^n$, and arbitrary message-dependent local CPTP encodings. The reference is retained and decoding may be collective. The ordinary limit exists and satisfies
--
--   $$C_{\rm ea}(\Phi)=\lim_{n\to\infty}\frac{C_{\rm ea}^{(1)}(\Phi^{\otimes n})}{n}=\max_{\rho\ge0,\,\operatorname{Tr}\rho=1} I(\rho;\Phi).$$
--
--   Here $I(\rho;\Phi)=H(\rho)+H(\Phi(\rho))-H((\operatorname{id}\otimes\Phi)(|\psi_\rho\rangle\langle\psi_\rho|))$, using a genuine purification of $\rho$. The maximum is attained. This characterizes the paper's regularized Holevo capacity.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 2, §II, equation (4): BSST entanglement-assisted classical capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.2, (4), including both directions (6),(14), normalized-input maximization,
and the existence of the ordinary block limit (3). -/
theorem bsstCapacity {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (N : Superop A C) (hN : IsChannel N) :
    Tendsto (assistedRate N) atTop (nhds (regularizedAssistedHolevo N)) ∧
    IsGreatest {v | ∃ rho : Matrix A A ℂ,
      IsDensityMatrix rho ∧ v = inputMutualInfo N rho} (regularizedAssistedHolevo N) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
