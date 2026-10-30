-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_measure_prepare_iff_polytope
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.measure_prepare_iff_polytope
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:14:02.952966+00:00
-- url     : https://prove2.me/theorems/7f99ce14-f4d3-4823-82ad-2018eb3a6095
-- title:
--   Proposition 18: finite measure-and-prepare programmability iff polytope
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. The normalized, reference-first Choi operator is $c_T=(\mathrm{id}_{d_1}\otimes T)(|\Omega\rangle\langle\Omega|)$, where $|\Omega\rangle=d_1^{-1/2}\sum_i|i,i\rangle$, with two input-sized factors before $T$ acts. A processor is one fixed CPTP map $P:\mathcal B(\mathcal H_1\otimes\mathbb C^p)\to\mathcal B(\mathcal H_2)$, chosen before the target channel. An $\varepsilon$-processor means that every target $T$ has a density program $\pi_T$ with $\frac12\|P(\cdot\otimes\pi_T)-T\|_\diamond\le\varepsilon$, including entangled reference inputs. Let $C$ be a nonempty convex set of CPTP maps. A measure-and-prepare processor has finitely many fixed target channels $T_j\in C$ and positive POVM effects $E_j$ summing to the program identity, with $P(A\otimes B)=\sum_j\operatorname{tr}(E_jB)T_j(A)$. Then
--
--   $$C\text{ has a finite exact measure-and-prepare processor}\ \Longleftrightarrow\ J_C=\{c_T:T\in C\}\text{ is a finite polytope}.$$
--
--   When these conditions hold, the program dimension can equal the finite number of extreme points of $J_C$, and every channel in $C$ has a unit pure program. Nonemptiness is the convention used by the source proof. This characterizes this special processor architecture.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 9, Proposition 18: finite measure-and-prepare programmability iff polytope

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

/-- PDF pp.9--10, Proposition 18: finite measure-and-prepare programmability
iff a polytope. Nonemptiness is the convention used by the proof. -/
theorem measure_prepare_iff_polytope (C : Set (Superop I O))
    (hne : C.Nonempty) (hconv : Convex ℝ C) (hchannels : ∀ T ∈ C, IsChannel T) :
    ((∃ p : ℕ, 0 < p ∧ ∃ processor : Superop (I × Fin p) O,
      ProgramsChannelClass processor C 0 ∧ FiniteMeasurePrepareProcessor processor C) ↔ Polytope (choiSet C)) ∧
    (Polytope (choiSet C) → ∃ p : ℕ,
      0 < p ∧ p = ((choiSet C).extremePoints ℝ).ncard ∧
      ∃ processor : Superop (I × Fin p) O,
        PureImplements processor C 0 ∧ FiniteMeasurePrepareProcessor processor C) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
