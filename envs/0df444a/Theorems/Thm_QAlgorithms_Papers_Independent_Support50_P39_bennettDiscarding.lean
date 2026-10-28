-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P39_bennettDiscarding
-- name    : QAlgorithms.Papers.Independent.Support50.P39.bennettDiscarding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:00:23.889711+00:00
-- url     : https://prove2.me/theorems/9a994e6d-3afe-4789-80de-68e96012f8bc
-- title:
--   Bennett’s local-discarding example increases clipped coherent information
-- statement:
--   Let $T,A,B$ be nonzero finite dimensional registers, with Alice owning $T$ and $A$ and Bob owning $B$. Let $\tau_T$ and $\sigma_{AB}$ be normalized density operators. Write $I^B(\omega)=\max\{S(\omega_B)-S(\omega),0\}$, with entropies in bits. Suppose $t=S(\tau)>0$ and $b=I^B(\sigma)>0$. Regard $\rho=\tau_T\otimes\sigma_{AB}$ as a state on $(T\otimes A):B$. Then
--
--   $$
--   \operatorname{Tr}_T\rho=\sigma,\qquad
--   I^B(\rho)=\max\{b-t,0\}<b=I^B(\operatorname{Tr}_T\rho).
--   $$
--
--   Discarding a mixed local factor therefore strictly increases the paper's clipped coherent information, including when $t\ge b$. The source attributes this example to Charles Bennett; its subsequent question about two-qubit states is not a theorem.
-- source:
--   Classical capacity of a noiseless quantum channel assisted by noisy entanglement, arXiv:quant-ph/0106080v3, PDF p. 6, Section 2, example due to Bennett

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:quant-ph/0106080v3, PDF p.6, Bennett's example (attributed result).
For t=S(tau)>0 and b=I^B(sigma)>0 the initial clipped information is
max(b-t,0), and actually discarding Alice's T factor gives sigma and strictly
increases coherent information. No two-qubit conjecture is asserted. -/
theorem bennettDiscarding {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq T] [DecidableEq A] [DecidableEq B]
    [Nonempty T] [Nonempty A] [Nonempty B]
    (tau : Matrix T T ℂ) (sigma : Matrix (A × B) (A × B) ℂ)
    (htau : IsDensityMatrix tau) (hsigma : IsDensityMatrix sigma)
    (ht : 0 < vnEntropy tau) (hb : 0 < clippedCoherentInformation sigma) :
    discardFirstAlice (productFactor tau sigma) = sigma ∧
    clippedCoherentInformation (productFactor tau sigma) =
      max (clippedCoherentInformation sigma - vnEntropy tau) 0 ∧
    clippedCoherentInformation (productFactor tau sigma) <
      clippedCoherentInformation (discardFirstAlice (productFactor tau sigma)) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P39
