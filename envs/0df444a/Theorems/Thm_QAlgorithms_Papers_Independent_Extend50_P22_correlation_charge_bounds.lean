-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_correlation_charge_bounds
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.correlation_charge_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:16:15.915082+00:00
-- url     : https://prove2.me/theorems/0ef4155e-fdec-4f26-9635-e562899a39df
-- title:
--   Theorem 9: correlation-derived bounds, Eqs.(B.9)–(B.10)
-- statement:
--   Let an isometry $V:L\to\bigotimes_{i=1}^n A_i$ encode a logical system of dimension $d\ge1$ into $n\ge1$ finite subsystems of positive dimensions $d_i$. A located erasure replaces erased sites by fixed pure states and supplies an orthogonal location flag. Write $\epsilon_{\rm worst}=\sqrt{1-f_{\rm worst}^2}$, where one CPTP recovery is optimized before minimizing root entanglement fidelity over all unit vectors on $L\otimes R$, with $R\simeq L$. Write $\epsilon_e=\sqrt{1-f_e^2}$ for optimal root entanglement fidelity at the normalized maximally entangled input. Unless specified otherwise, single-site erasure is uniform. For Hermitian charges satisfying $(\sum_iT_i)V=V(T_L-\nu I)$, let $e_i$ denote the optimal average-entanglement error after erasure of site $i$. Let $q_i>0$ sum to one, and let $e_q$ be the same error for the flagged mixture with these probabilities. Then $$\frac{\|T_L-\operatorname{tr}(T_L)I/d\|_1}{2d}\le\sum_i\Delta T_i e_i,\qquad \frac{\|T_L-\operatorname{tr}(T_L)I/d\|_1}{2d}\le\max_i\frac{\Delta T_i}{q_i}\,e_q.$$ Both conclusions retain the theorem’s printed factor two.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 36, Theorem 9: correlation-derived bounds, Eqs.(B.9)–(B.10)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.36, Theorem 9, (B.9),(B.10). Both clauses retain the printed factor 1/(2d). -/
theorem correlation_charge_bounds {d n : ℕ} (c : CovariantErasureCodeData d n)
    (TL : Matrix (Fin d) (Fin d) ℂ)
    (Ti : (i : Fin n) → Matrix (Fin (c.dims i)) (Fin (c.dims i)) ℂ)
    (hc : ChargeCovariant c TL Ti) (q : Fin n → ℝ)
    (hq : ∀ i, 0 < q i) (hsum : ∑ i, q i = 1) :
    meanSpread TL ≤ ∑ i, chargeRange (Ti i) *
      errorE (erase {i} c.reset ∘ conjSuperop c.V) ∧
    meanSpread TL ≤ finiteMax c.sitesPositive (fun i => chargeRange (Ti i) / q i) *
      errorE (c.noise q) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
