-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_guessing_probability
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.guessing_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:15:12.020433+00:00
-- url     : https://prove2.me/theorems/7919bb8a-5177-4541-879d-9b83592d681f
-- title:
--   Lemma A.8: guessing probability
-- statement:
--   Let $K=\{1,\ldots,d\}$ with $d\ge1$, let $p_k\ge0$ sum to one, and let $\rho_E^k$ be normalized positive trace-class states on an arbitrary separable memory space $E$. Form $\rho_{KE}=\sum_k p_k|k\rangle\langle k|\otimes\rho_E^k$, let $\rho_E$ be its actual marginal, and let $\tau_K=I_K/d$. Optimizing over all $d$-outcome POVMs of bounded operators on $E$ gives
--
--   $$p_{\mathrm{guess}}(K|E)_\rho\le\frac1d+D(\rho_{KE},\tau_K\otimes\rho_E).$$
--
--   The memory has no dimension cutoff; zero ensemble weights are allowed. This bounds the operational guessing probability by uniform guessing plus the secrecy distance.
--
--   **Formalization Note** The finite real guessing probability is embedded into the extended nonnegative reals to compare with half the nuclear norm without a potentially lossy conversion of infinity to a real.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 43, Lemma A.8: guessing probability

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.42--43, Lemma A.8: classical-key guessing, with an arbitrary
countable memory basis and actual bounded-operator POVMs. The reference uses
the actual marginal of the complete cq ensemble, including zero-weight keys.
The extended-nonnegative form is equivalent to the source's real inequality
because the distance of normalized trace-class states is finite. -/
theorem guessing_probability {d : ℕ} (hd : 0 < d) {E : Type} [Countable E]
    (p : Fin d → ℝ) (hp : ∀ k, 0 ≤ p k) (hnormalized : ∑ k, p k = 1)
    (rho : Fin d → State E) :
    ENNReal.ofReal (memoryGuess p rho) ≤ ENNReal.ofReal (1 / (d : ℝ)) +
      nuclearDistance (cqState p (fun k => (rho k).coefficients))
        (uniformReference (partialTraceFirst (cqState p (fun k => (rho k).coefficients)))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
