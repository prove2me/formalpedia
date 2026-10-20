-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_example8
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.example8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:34:24.750972+00:00
-- url     : https://prove2.me/theorems/0cdb1627-f0ea-413f-bd7a-de68c6388ecf
-- title:
--   Quantum-classical sources and accessible information
-- statement:
--   Let $E=\{p(x),\rho_x^A\}$ be a finite ensemble, and let $\omega^{AB}=\sum_xp(x)\rho_x^A\otimes|x\rangle\langle x|^B$. Communication is still one-way from Alice to Bob. Let $I_{\rm acc}(E)$ be the supremum of classical mutual information between $X$ and the outcome of a finite POVM on the ensemble states. For every integer $L\ge1$,
--
--   $$D(\omega,\infty)=D^{(L)}(\omega,\infty)=D^{(1)}(\omega,\infty)=I_{\rm acc}(E).$$
--
--   The quantities $D$ are operational excess common-randomness rates with the paper’s disagreement and Shannon-entropy criterion. The example identifies the reversed placement of a cq source with accessible information.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 15, Example 8: quantum-classical sources and accessible information

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section QuantumStatements

variable {A B A2 B2 : Type} [Fintype A] [Fintype B] [Fintype A2] [Fintype B2]
  [DecidableEq A] [DecidableEq B] [DecidableEq A2] [DecidableEq B2]
  [Nonempty A] [Nonempty B] [Nonempty A2] [Nonempty B2]

/-- PDF pp.15--16, Example 8: reverse cq placement, with every positive blocklength. -/
theorem example8 {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq X] [DecidableEq Q]
    [Nonempty X] [Nonempty Q] (E : CQData X Q) (hE : E.Valid) (L : ℕ) (hL : 0 < L) :
    total (qcDensity E) = blockTotal (qcDensity E) L ∧
    blockTotal (qcDensity E) L = fixedTotal (qcDensity E) ∧
    fixedTotal (qcDensity E) = accessibleInformation E := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
