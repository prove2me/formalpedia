-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_twisted_separable_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.twisted_separable_relative_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:19:53.027369+00:00
-- url     : https://prove2.me/theorems/61e92eee-53bf-49ba-aba9-b0e113704319
-- title:
--   Lemma 7: relative entropy of twisted separable marginals
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Fix a $B$-twisting $U$ and let $\omega$ be a separable state across $AA':BB'$. Write $\sigma_{AB}=\operatorname{Tr}_{A'B'}U\omega U^\dagger$ and let $P_d^+$ project onto the maximally entangled key state. Then
--
--   $$D_2(P_d^+\Vert\sigma_{AB})\ge\log_2d.$$
--
--   Here $D_2$ is Umegaki relative entropy in bits, infinite when its first support is not contained in the second. This bound controls marginals of the fixed twisted separable set.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 27, Lemma 7: relative entropy of twisted separable marginals

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

/-- PDF p.27, Lemma 7; pp.39–40: fixed twisting and the AA':BB' separable cut.
Support violations give infinite relative entropy. -/
theorem twisted_separable_relative_entropy {d : ℕ} [NeZero d] {S T : Type*}
    [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (U : Key d → Matrix.unitaryGroup (S × T) ℂ)
    (omega : Op (Key d × (S × T))) (homega : Entanglement.IsSeparableDensity (partyCut omega)) :
    ENNReal.ofReal (logBits d) ≤
      relativeEntropyBits (bellProjector d) (traceRight (twist U omega)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
