-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_no_universal_exact_cloner
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.no_universal_exact_cloner
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:17:59.983765+00:00
-- url     : https://prove2.me/theorems/1f743454-4418-4c41-93c7-e8f32196fe46
-- title:
--   No universal exact cloner for classical permutations or quantum gates
-- statement:
--   There is no common randomized classical circuit which, given arbitrary input letters $x,y\in\{a,b,c\}$ and only one ordinary evaluation of an unknown permutation $f$ of these letters, outputs $(f(x),f(y))$ with probability one for every permutation and every input pair. The query and output distributions are fixed independently of $f$.
--
--   Likewise, for every integer $d\ge2$, no common deterministic quantum circuit with arbitrary finite memory, CPTP preprocessing and CPTP postprocessing can use an unknown $d$-dimensional unitary gate once and implement its independent tensor square on every input:
--
--   $$\neg\exists\mathcal N\ \forall U\in U(d),\quad\mathcal N[\mathcal U]=\mathcal U\otimes\mathcal U.$$
--
--   These are two access models: the classical clause uses an ordinary evaluation, while the quantum clause allows coherent quantum processing. Physical unitary channels are compared modulo global phase.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 1, Unnumbered corollaries

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.1: the two distinct corollaries. The first is ordinary classical access
to all three-letter permutations; the second is a common deterministic quantum
network for all d-dimensional unitary channels, compared modulo global phase. -/
theorem no_universal_exact_cloner (d : ℕ) (hd : 2 ≤ d) :
    (¬ ∃ net : ClassicalOneCall, ∀ f : Equiv.Perm (Fin 3), ∀ x : PairReg 3,
      net.probability f x (f x.1,f x.2) = 1) ∧
    (¬ ∃ net : OneCall d, ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), OneCall.run net U = targetChannel U) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
