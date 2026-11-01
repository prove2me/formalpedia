-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_hardy_maximal_distribution_unique
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_maximal_distribution_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:40:49.435787+00:00
-- url     : https://prove2.me/theorems/5233dd77-509c-4560-a721-06ee3e9c9321
-- title:
--   Unique quantum behavior at maximal Hardy success
-- statement:
--   Consider binary settings $A,B$ and outcomes $a,b$. A finite quantum realization consists of arbitrary finite local dimensions $d_A,d_B$, one positive semidefinite density matrix $\rho$ of trace one on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, and binary POVMs $\{M_{A,a}\}_a$, $\{N_{B,b}\}_b$ for each local input. Its entire behavior is $p(a,b\mid A,B)=\operatorname{Re}\operatorname{Tr}[(M_{A,a}\otimes N_{B,b})\rho]$. There exists exactly one such behavior satisfying $p(00\mid00)>0$, $p(00\mid10)=p(00\mid01)=p(11\mid11)=0$, and $p(00\mid00)=(5\sqrt5-11)/2$. Uniqueness is equality of all sixteen conditional probabilities across all finite realizations.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 3, II B: maximal-Hardy uniqueness [22]

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- II B, PDF p.3, citing [22]: the ideal Hardy constraints at maximal success
specify a unique full quantum probability distribution. Realizations range over all finite
local dimensions, density matrices and binary POVMs, as in IV A; existence is part of the
conclusion. The claim is about the distribution and does not assert a local-isometry or
sequential-security conclusion. -/
theorem hardy_maximal_distribution_unique :
    ∃! p : Behavior, HasFiniteQuantumRealization p ∧ HardyConditions p ∧
      p false false false false = (5 * Real.sqrt 5 - 11) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
