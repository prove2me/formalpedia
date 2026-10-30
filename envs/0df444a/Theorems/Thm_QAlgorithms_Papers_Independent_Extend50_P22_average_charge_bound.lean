-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_average_charge_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.average_charge_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:13:00.254387+00:00
-- url     : https://prove2.me/theorems/30b1462f-7f04-4919-9068-ace71400be25
-- title:
--   Unnumbered average-entanglement charge bound, Eq.(27)
-- statement:
--   Let an isometry $V:L\to\bigotimes_{i=1}^n A_i$ encode a logical system of dimension $d\ge1$ into $n\ge1$ finite subsystems of positive dimensions $d_i$. A located erasure replaces erased sites by fixed pure states and supplies an orthogonal location flag. Write $\epsilon_{\rm worst}=\sqrt{1-f_{\rm worst}^2}$, where one CPTP recovery is optimized before minimizing root entanglement fidelity over all unit vectors on $L\otimes R$, with $R\simeq L$. Write $\epsilon_e=\sqrt{1-f_e^2}$ for optimal root entanglement fidelity at the normalized maximally entangled input. Unless specified otherwise, single-site erasure is uniform. For Hermitian logical and local charges satisfying $(\sum_iT_i)V=V(T_L-\nu I)$, define $S(T_L)=\|T_L-\operatorname{tr}(T_L)I/d\|_1/(2d)$, with trace norm $\|\cdot\|_1$. Then $$S(T_L)\le n\max_i\Delta T_i\,\epsilon_e.$$ The mean-centered spread samples the full logical spectrum.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 8, Unnumbered average-entanglement charge bound, Eq.(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.8, (27). Average-entanglement fidelity, retaining the factor 1/(2d). -/
theorem average_charge_bound {d n : ℕ} (c : CovariantErasureCodeData d n)
    (TL : Matrix (Fin d) (Fin d) ℂ)
    (Ti : (i : Fin n) → Matrix (Fin (c.dims i)) (Fin (c.dims i)) ℂ)
    (hc : ChargeCovariant c TL Ti) :
    meanSpread TL ≤ n * finiteMax c.sitesPositive (fun i => chargeRange (Ti i)) *
      errorE c.uniformNoise := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
