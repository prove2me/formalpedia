-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_common_preprocessing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.common_preprocessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:26:15.363037+00:00
-- url     : https://prove2.me/theorems/88168cb9-75ef-458e-a9ef-0f8792c0e10f
-- title:
--   Common preprocessing realization of a whole supermeasurement
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. Let $X$ be a finite nonempty outcome set, and let $\{\Theta_x:A\to B\}_{x\in X}$ be a supermeasurement: every branch is CPTNI-preserving and the branches sum to a superchannel. There exist a common finite nonzero memory $E_0$, a channel $\Gamma_{\mathrm{pre}}:B_0\to A_0E_0$, and CPTNI maps $\Gamma_{\mathrm{post},x}:A_1E_0\to B_1$, whose sum is CPTP, such that for every $x$, every complex-linear input map $N$, and every operator $Z$ on $B_0$,
--
--   $$\Theta_x[N](Z)=\Gamma_{\mathrm{post},x}\!\left[(N\otimes I_{E_0})(\Gamma_{\mathrm{pre}}(Z))\right].$$
--
--   The shared preprocessing and the whole family of postprocessings are chosen before $x,N,Z$. Equivalently their Choi matrices satisfy the displayed identity of Proposition E.1 with unnormalized maximally entangled vectors and the stated copies. This gives a joint physical realization of the entire instrument.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 18, Proposition E.1; pp.4,19

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section QuantumResults

variable {A0 A1 B0 B1 : Type}

variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]

variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

/-- PDF pp.4,18–19, Proposition E.1: common preprocessing and finite memory
work for every branch and input map. Postprocessings form an instrument.
Equality on all maps/operators is the full-map form of the displayed Choi identity. -/
theorem common_preprocessing {X : Type} [Fintype X] [Nonempty X]
    (S : X → Supermap A0 A1 B0 B1) (hS : IsSupermeasurement S) :
    ∃ e : ℕ, 0 < e ∧ ∃ pre : QMap B0 (A0 × Fin e), IsChannel pre ∧
      ∃ post : X → QMap (A1 × Fin e) B1,
        (∀ x, IsCPTNI (post x)) ∧ IsChannel (∑ x, post x) ∧
        ∀ (x : X) (N : QMap A0 A1) (rho : Op B0),
          superApply (S x) N rho = combApply pre (post x) N rho := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
