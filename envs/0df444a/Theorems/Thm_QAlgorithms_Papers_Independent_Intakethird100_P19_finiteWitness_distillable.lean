-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_finiteWitness_distillable
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.finiteWitness_distillable
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:40:27.856891+00:00
-- url     : https://prove2.me/theorems/5f115cc7-2095-4bf2-81b7-335965e026bf
-- title:
--   Theorem 15: distillable output undetected by finitely many witnesses
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. LOCC-distillable means that channels $\Lambda_n$ obtainable by local operations and classical communication satisfy $\|\Lambda_n(\rho^{\otimes n})-\phi_2^+\|_1\to0$, with copies regrouped by party. Fix input dimensions $a,b\ge1$, output dimensions $c,d\ge2$, and finitely many Hermitian witnesses $W_i$ across $A_{\rm out}A_{\rm in}:B_{\rm out}B_{\rm in}$. The family may be empty. There exists a state $\sigma$ on the output register and the channel $\Lambda(X)=\operatorname{Tr}(X)\sigma$ such that
--
--   $$\sigma\text{ is LOCC-distillable},\quad\operatorname{Tr}(W_iJ(\Lambda))\ge0\ (\forall i),\quad\Lambda(\rho)=\sigma\ (\forall\rho\text{ state}).$$
--
--   One fixed constant channel works for all input states.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 18, Theorem 15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Theorem 15, PDF p.18: a finite witness family admits a constant channel
to a distillable state. Correct the printed input/output subscript to A2 B2 A1 B1.
Both output local dimensions must be at least two, as the proof requires.
The constructed channel works uniformly for all input density matrices. -/
theorem finiteWitness_distillable {a b c d n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (W : Fin n → Op ((Fin c × Fin a) × (Fin d × Fin b)))
    (hw : ∀ i, Witness (W i)) :
    ∃ sigma : Bip c d, LOCCDistillable sigma ∧
      IsChannel (fun X : Bip a b => X.trace • sigma) ∧
      Undetected W (fun X : Bip a b => X.trace • sigma) ∧
      ∀ rho : Bip a b, IsDensityMatrix rho →
        (fun X : Bip a b => X.trace • sigma) rho = sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
