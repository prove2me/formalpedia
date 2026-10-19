-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_composition_destroys_domination
-- name    : QAlgorithms.Papers.Independent.Information100.P62.composition_destroys_domination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T22:02:59.374343+00:00
-- url     : https://prove2.me/theorems/4cff6790-6503-4c13-847c-14258d77a52a
-- title:
--   Proposition B.3: domination can fail under composition
-- statement:
--   For the channel $\Phi$ on $M_4(\mathbb C)$ defined in (6.29), with $|\pm\rangle=(|0\rangle\pm|2\rangle)/\sqrt2$, $E_0=|0\rangle\langle+|+|1\rangle\langle1|+|3\rangle\langle-|$ and $E_1=|-\rangle\langle3|$,
--   $$A_{\rm dom}(\Phi)\cong M_3(\mathbb C),\qquad\max\mathcal T(\Phi\circ\Phi)=\{M_2(\mathbb C),\mathbb C^3\}.$$
--   Consequently its sequential square has no dominating transmittable algebra. The square denotes composition, not a tensor product.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 62, Proposition B.3: domination can fail under composition

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.62, 63, Proposition B.3: domination can fail under composition. -/
theorem composition_destroys_domination :
    IsChannel compositionExample ∧ Dominating compositionExample (quantum 3) ∧
    maximals (compositionExample ∘ compositionExample) = {quantum 2, classical 3} ∧
    ¬ HasDominating (compositionExample ∘ compositionExample) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
