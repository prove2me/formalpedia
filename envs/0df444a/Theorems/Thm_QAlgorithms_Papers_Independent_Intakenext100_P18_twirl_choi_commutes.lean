-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_twirl_choi_commutes
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.twirl_choi_commutes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:26:46.454987+00:00
-- url     : https://prove2.me/theorems/0506f0f3-b271-43ab-9e0a-cca37cc690b4
-- title:
--   Choi correspondence commutes with state and channel twirling
-- statement:
--   Let $d\ge1$ and let $\Lambda$ be any completely positive trace-preserving map. Write $J(\Lambda)=(\operatorname{id}\otimes\Lambda)(P_+)$ for the normalized reference-first Choi state. Define channel twirling by $\mathcal T(\Lambda)(X)=\int U^\dagger\Lambda(UXU^\dagger)U\,dU$, and state twirling by $\mathcal S(\rho)=\int(U\otimes\overline U)\rho(U\otimes\overline U)^\dagger\,dU$, both using normalized Haar measure on $U(d)$. Then
--
--   $$J(\mathcal T(\Lambda))=\mathcal S(J(\Lambda)).$$
--
--   This makes the two twirling constructions compatible with the actual Choi map. The bar denotes entrywise complex conjugation, rather than Hermitian adjoint.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 6, §III.D, eq.(22): state and channel twirling commute with the Choi map

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF pp.6--7, (22)--(24): Choi and state/channel twirls commute.
The state twirl uses U tensor conjugate U, exactly as in (17). -/
theorem twirl_choi_commutes (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    choiState (QuditFidelity.haarTwirl d hd E) =
      stateTwirl d (choiState E) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
