-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_pure_program_conversion
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.pure_program_conversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:10:45.984998+00:00
-- url     : https://prove2.me/theorems/96958a30-a90a-41ce-bfca-811bca0ac09b
-- title:
--   Remark 13: conversion to pure programs
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. A processor is one fixed CPTP map $P:\mathcal B(\mathcal H_1\otimes\mathbb C^p)\to\mathcal B(\mathcal H_2)$, chosen before the target channel. An $\varepsilon$-processor means that every target $T$ has a density program $\pi_T$ with $\frac12\|P(\cdot\otimes\pi_T)-T\|_\diamond\le\varepsilon$, including entangled reference inputs. For every processor with program dimension $p>0$, there are two fixed CPTP processors which simulate every channel induced by any original density program exactly using a unit pure program. With $D=d_1^2(d_2^2-1)+1$, their positive dimensions $q_1,q_2$ satisfy
--
--   $$q_1\le p^2,\qquad q_2\le p\min\{p,D\}.$$
--
--   For each original program the induced superoperators agree on every operator. The refined construction can replace the original program by another program of smaller rank; it preserves any original approximation guarantee.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 6, Remark 13: conversion to pure programs

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible EquivalentModels)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

namespace QAlgorithms.Papers.Independent.Extend50.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section General

variable {G I O : Type*} [Group G] [TopologicalSpace G]

variable [Fintype I] [DecidableEq I] [inputNonempty : Nonempty I]

variable [Fintype O] [DecidableEq O] [outputNonempty : Nonempty O]

include inputNonempty outputNonempty

/-- PDF p.6, Remark 13: both fixed pure-program simulations and their bounds.
The refined simulation may replace a program by a lower-rank one implementing
the same channel; it need not purify the original program. -/
theorem pure_program_conversion (p : ℕ) (hp : 0 < p)
    (processor : Superop (I × Fin p) O) (hP : IsChannel processor) :
    (∃ q : ℕ, 0 < q ∧ q ≤ p ^ 2 ∧ ∃ newProcessor : Superop (I × Fin q) O,
      PureSimulation p q processor newProcessor) ∧
    (∃ q : ℕ, 0 < q ∧ q ≤ p * min p (caratheodorySize (Fintype.card I) (Fintype.card O)) ∧
      ∃ newProcessor : Superop (I × Fin q) O, PureSimulation p q processor newProcessor) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
