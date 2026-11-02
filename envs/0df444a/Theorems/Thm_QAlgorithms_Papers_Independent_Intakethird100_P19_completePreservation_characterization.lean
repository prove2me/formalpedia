-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_completePreservation_characterization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.completePreservation_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:41:29.716305+00:00
-- url     : https://prove2.me/theorems/1a3d5cae-4a92-4b8a-9d3c-5aa7a10e8114
-- title:
--   Proposition 17: complete preservation and Choi classes
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. Let $d\ge1$ and let $\Lambda$ be any completely positive map from $d\times d$ to an arbitrary positive-dimensional bipartite register. Trace preservation is not assumed. Then both chains hold:
--
--   $$\Lambda\text{ separable}\ \Longleftrightarrow\ \Lambda\text{ is }d\text{-non-entangling}\ \Longleftrightarrow\ \Lambda\text{ is completely non-entangling},$$
--
--   $$J(\Lambda)\text{ PPT}\ \Longleftrightarrow\ \Lambda\text{ is }d\text{-PPT-preserving}\ \Longleftrightarrow\ \Lambda\text{ is completely PPT-preserving}.$$
--
--   The $k$-preservation conditions amplify by the identity on a $k$-dimensional ancilla at each party; complete preservation quantifies over all $k\ge1$.
--
--   This identifies the completely preserving classes with their grouped Choi classes.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 20, Proposition 17

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

/-- Proposition 17, PDF pp.20-21: both respectively branches, for CP maps
without trace preservation. The local input dimension d=1 is included. -/
theorem completePreservation_characterization {d a b : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (L : Superop (Fin d × Fin d) (Fin a × Fin b)) (hcp : CP L) :
    ((SEP L ↔ KNE d L) ∧ (KNE d L ↔ CompleteNE L)) ∧
    ((ChoiPPT L ↔ KPPT d L) ∧ (KPPT d L ↔ CompletePPT L)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
