-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_entangled_remote_preparation
-- name    : QAlgorithms.Papers.Independent.Support21.P19.entangled_remote_preparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:09:31.08873+00:00
-- url     : https://prove2.me/theorems/fb33b3d1-94d6-4e11-aca3-d81741d1faa0
-- title:
--   Eq. (7): coherent entangled remote-state preparation
-- statement:
--   Let $\mathcal E=\{p_i,|\psi_i\rangle_{AB}\}$ be a normalized finite ensemble of bipartite pure states. Put $\rho_i=\operatorname{Tr}_A|\psi_i\rangle\langle\psi_i|$, $E=\sum_i p_i S(\rho_i)$, and $\chi=S(\sum_i p_i\rho_i)-E$, with entropy in bits. Then
--
--   $$
--   \chi\,[q\to qq]+E\,[qq]\ge\mathcal E\qquad(a).
--   $$
--
--   Here the target for block length $n$ is $U_\psi^{\otimes n}$ on the entire span of probability-typical label sequences, with Alice retaining the labels. For every positive error, rate and typicality slack, a sufficiently small fixed positive typicality tolerance and all sufficiently large $n$ admit a sequential protocol using at most $n(\chi+\delta)$ integer cobit calls and $n(E+\delta)$ input EPR pairs. Error is uniform over all coherent superpositions in that span and all finite references. Zero-probability letters are absent. This specifies coherent preparation, rather than a classical mixture of ensemble states.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 3, Eq. (7): coherent entangled remote-state preparation

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3–4, Eq. (7): coherent entangled remote-state preparation at chi cobits and E ebits. -/
theorem entangled_remote_preparation {a b : ℕ} (E : BipartitePureData a b) :
    Prepares E 0 (bobHolevoBits E.prob E.vector) (averageE E.prob E.vector) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
