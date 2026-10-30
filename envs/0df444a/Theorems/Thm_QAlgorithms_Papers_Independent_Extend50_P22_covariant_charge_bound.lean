-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_covariant_charge_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.covariant_charge_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:11:51.709509+00:00
-- url     : https://prove2.me/theorems/a757b43f-ec0e-4637-9160-6d39786406d3
-- title:
--   Theorem 1, Eq.(26): covariant-code inaccuracy (original paper-result seed)
-- statement:
--   Let an isometry $V:L\to\bigotimes_{i=1}^n A_i$ encode a logical system of dimension $d\ge1$ into $n\ge1$ finite subsystems of positive dimensions $d_i$. A located erasure replaces erased sites by fixed pure states and supplies an orthogonal location flag. Write $\epsilon_{\rm worst}=\sqrt{1-f_{\rm worst}^2}$, where one CPTP recovery is optimized before minimizing root entanglement fidelity over all unit vectors on $L\otimes R$, with $R\simeq L$. Write $\epsilon_e=\sqrt{1-f_e^2}$ for optimal root entanglement fidelity at the normalized maximally entangled input. Unless specified otherwise, single-site erasure is uniform. Let $T_L,T_i$ be Hermitian charges with $(\sum_i T_i)V=V(T_L-\nu I)$ for some real offset $\nu$, where each $T_i$ acts on its own site. For a Hermitian operator $T$, let $\Delta T$ denote its largest eigenvalue minus its smallest. Then $$\Delta T_L\le2n\max_i\Delta T_i\,\epsilon_{\rm worst}.$$ This is the finite charge-range obstruction, including zero ranges.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 8, Theorem 1, Eq.(26): covariant-code inaccuracy (original paper-result seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.8, Theorem 1, (26). Cross multiplication retains zero-range cases. -/
theorem covariant_charge_bound {d n : ℕ} (c : CovariantErasureCodeData d n)
    (TL : Matrix (Fin d) (Fin d) ℂ)
    (Ti : (i : Fin n) → Matrix (Fin (c.dims i)) (Fin (c.dims i)) ℂ)
    (hc : ChargeCovariant c TL Ti) :
    chargeRange TL ≤ 2 * n * finiteMax c.sitesPositive (fun i => chargeRange (Ti i)) *
      errorWorst c.uniformNoise := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
