-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_ppt_approximates_private_bits
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.ppt_approximates_private_bits
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:19:14.150112+00:00
-- url     : https://prove2.me/theorems/010d7ad1-f0e7-456e-831b-677beec4d96b
-- title:
--   Theorem 7: PPT approximation of private bits
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   For every $\epsilon>0$, there exist positive finite shield dimensions and states $\rho,\gamma$ on the same two-qubit-key and shield registers such that
--
--   $$\rho^{\Gamma_{BB'}}\succeq0,\qquad\gamma\text{ is a private bit},\qquad\|\rho-\gamma\|_1\le\epsilon.$$
--
--   The shield dimensions may depend on $\epsilon$. Thus finite-dimensional PPT states approximate private bits arbitrarily well without specifying one fixed finite-dimensional target.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 25, Theorem 7: PPT approximation of private bits

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.25, Theorem 7: shield dimensions may grow as accuracy increases. -/
theorem ppt_approximates_private_bits (eps : ℝ) (heps : 0 < eps) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∃ rho gamma : Op (Key 2 × (Fin a × Fin b)),
        IsDensityMatrix rho ∧ (transposeBob rho).PosSemidef ∧
        IsPrivate gamma ∧ traceNorm (rho-gamma) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
