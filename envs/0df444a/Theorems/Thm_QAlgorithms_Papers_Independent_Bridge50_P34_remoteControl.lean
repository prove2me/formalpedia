-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P34_remoteControl
-- name    : QAlgorithms.Papers.Independent.Bridge50.P34.remoteControl
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:07:47.758651+00:00
-- url     : https://prove2.me/theorems/127eb676-9b13-4016-b4d9-d3236f8e96ea
-- title:
--   Reference measurement representation of formation
-- statement:
--   Let $\rho$ be a density matrix on finite complex systems $A\otimes B$ of positive dimensions $d,d'$. Let $\Psi$ be any unit purification of $\rho$ on $(A\otimes B)\otimes R$, where $\dim R=d^2d'^2$. For an orthonormal basis $u=(u_m)$ of $R$, form the unnormalized outcome vectors $v_m=(I_{AB}\otimes\langle u_m|)\Psi$. Let
--
--   $$
--   \omega_{AR'}(u)=\sum_m\operatorname{Tr}_B|v_m\rangle\langle v_m|\otimes|m\rangle\langle m|,\qquad p_m=\langle v_m|v_m\rangle.
--   $$
--
--   Write $\omega_{R'}=\operatorname{Tr}_A\omega_{AR'}$, $S$ for bit entropy, $H(p)=-\sum_m p_m\log_2p_m$ with zero terms interpreted as zero, and $E_F$ for the finite pure-state formation convex roof. Every basis satisfies
--
--   $$
--   E_F(\rho)\le S(\omega_{AR'}(u))-S(\omega_{R'}(u)).
--   $$
--
--   There exists a basis attaining equality, and for that basis $S(\omega_{R'})=H(p)$ and $S(\omega_{AR'})=H(p)+E_F(\rho)$. The result constructs an optimizing measurement for the given purification; zero-probability outcomes require no normalization.
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, PDF p. 3, Remote-control representation of formation, (11)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P34

attribute [local instance] Classical.propDecidable Classical.decEq

-- Accepted definition providers, authorized by the independent-paper workflow.

open QAlgorithms.Papers.Independent.Information100.P08 (formation bellVector)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Support50.P42 (outcomeEntropy)

-- The supplied diagnostic timed out while elaborating the remote-control statement.

set_option maxHeartbeats 800000

/-- PDF pp.2–3, (11)–(12): EVERY reference basis gives an upper bound and
SOME basis attains it, for the supplied purification on dim R=d^2*dprime^2.
The reference outcome entropy identities are conclusions, not premises. -/
theorem remoteControl {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ ((A × B) × Fin ((Fintype.card A)^2 * (Fintype.card B)^2)))
    (hpsi : ‖psi‖ = 1) (hpurifies : traceRight (pureDensity psi) = rho) :
    (∀ U : Matrix.unitaryGroup (Fin ((Fintype.card A)^2 * (Fintype.card B)^2)) ℂ,
      formation rho ≤ vnEntropy (measuredAR psi U) - vnEntropy (traceLeft (measuredAR psi U))) ∧
    (∃ U : Matrix.unitaryGroup (Fin ((Fintype.card A)^2 * (Fintype.card B)^2)) ℂ,
      formation rho = vnEntropy (measuredAR psi U) - vnEntropy (traceLeft (measuredAR psi U)) ∧
      vnEntropy (traceLeft (measuredAR psi U)) = outcomeEntropy (outcomeProbability psi U) ∧
      vnEntropy (measuredAR psi U) = outcomeEntropy (outcomeProbability psi U) + formation rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P34

end
