-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_coherent_hsw
-- name    : QAlgorithms.Papers.Independent.Support21.P19.coherent_hsw
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:57:32.22627+00:00
-- url     : https://prove2.me/theorems/8feddfbc-207c-499c-b70b-6ec8e1b3b077
-- title:
--   Lemma 2 (coherent HSW)
-- statement:
--   Let $\{p_x,|\psi_x\rangle_{AB}\}_{x=1}^l$ be a finite ensemble, with $p_x\ge0$, $\sum_xp_x=1$, and every vector normalized. Let $U_\psi$ be the isometry $|x\rangle_A\mapsto|x\rangle_A|\psi_x\rangle_{AB}$. With logarithms in base two, define $\rho_x=\operatorname{Tr}_A|\psi_x\rangle\langle\psi_x|$, $E=\sum_xp_x S(\rho_x)$, and $\chi=S(\sum_xp_x\rho_x)-E$. Then
--
--   $$
--   U_\psi\ge\chi\,[q\to qq]+E\,[qq]\qquad(a).
--   $$
--
--   The output EPR pairs are decoupled from the coherently copied message. The assertion uses integer resource counts, arbitrary rate slack and uniformly vanishing error on unknown superpositions and reference extensions. It identifies both communication and entanglement obtainable from the controlled ensemble isometry.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 2, Lemma 2 (coherent HSW)

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, Lemma 2: coherent HSW, including the decoupled output E-ebit rate. -/
theorem coherent_hsw {a b : ℕ} (E : BipartitePureData a b) :
    AchievesTransmission (ensembleResource E) (cobitChannel 2) (bobHolevoBits E.prob E.vector)
      (-averageE E.prob E.vector) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
