-- Prove2me | Theorems.Thm_SpectrumLB_proposition_3_5
-- name    : SpectrumLB.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:39:43.304213+00:00
-- url     : https://prove2.me/theorems/2b9dc53a-4b80-44e3-8bba-428192e7b49a
-- title:
--   Proposition 3.5 and Eq. (3.10) — $\mathbf E[X]=\nu_a\mathbf 1$ and $\mathbf E[X^{\otimes n}]=\nu_a^n\prod_tf_a(\widetilde J_t)$
-- statement:
--   Let $a_1,\dots,a_K$ be positive integers, $d$ a multiple of each $a_i$, and $X\sim\mathrm{PRP}_d(a)$. Then
--
--   $$
--   \mathbf E[X]=\nu_a\cdot\mathbf 1,\qquad \nu_a=\frac1{a_1a_2\cdots a_K},
--   $$
--
--   and for every $n$,
--
--   $$
--   \mathbf E\big[X^{\otimes n}\big]=\nu_a^{\,n}\prod_{t=1}^n f_a(\widetilde J_t),\qquad f_a(z)=\prod_{i=1}^K\frac{1+a_iz}{1+z},
--   $$
--
--   with $\widetilde J_t=J_t/d$. The tensor moments of the product of random projections are thus explicit functions of the Jucys–Murphy elements, which is what makes the two hard ensembles comparable.
--
--   Differences from the source:
--   - encoding: X ∼ PRP_d(a) → X = prpMatrix a U with U distributed as K independent Haar unitaries; expectations entrywise; reason: Definition 3.4 defines PRP_d(a) as this law
--   - encoding: f_a(J̃_t) → (∏_i (1 + a_i J̃_t)) · ((1 + J̃_t)⁻¹)^K; reason: the factors commute; same operator
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 3.4, Eq. (3.10), and Proposition 3.5, Eq. (3.11), p. 14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_SpectrumLB_jm
import Definitions.Def_SpectrumLB_haarK
import Definitions.Def_SpectrumLB_prpMatrix
import Definitions.Def_WildeQIT_Covering_expectation
import Definitions.Def_SpectrumLB_nuA
import Definitions.Def_SpectrumLB_fAOp

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Proposition 3.5 with Eq. (3.10) (tensor moments of PRP).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 3.4, Eq. (3.10), and Proposition 3.5, Eq. (3.11), p. 14: "E[X] = ν_a · 1,
ν_a := 1/(a_1 a_2 ⋯ a_K)" and "for X ∼ PRP_d(a_1, …, a_K), E[X^{⊗n}] = ν_a^n · ∏_{t=1}^n f_a(J̃_t), where
f_a(z) = ∏_{i=1}^K (1 + a_i z)/(1 + z)."

**Formalization Note.** `X ∼ PRP_d(a)` is `prpMatrix a U` with `U ∼ haarK d K`; expectations are entrywise.
`a_i > 0` and `a_i ∣ d` are Definition 3.4's hypotheses. `J̃_t = d⁻¹ J_t`; `f_a(J̃_t)` is `fAOp a J̃_t`. -/
theorem proposition_3_5 (d K : ℕ) (a : Fin K → ℕ) (ha : ∀ i, 0 < a i) (hd : ∀ i, a i ∣ d) :
    WildeQIT.Covering.expectation (haarK d K) (prpMatrix a) = (nuA a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
    ∀ n : ℕ, WildeQIT.Covering.expectation (haarK d K) (fun U => QAlgorithms.piKron n (prpMatrix a U)) =
      ((nuA a : ℂ) ^ n) • (List.ofFn fun t : Fin n => fAOp a ((d : ℂ)⁻¹ • jm d t)).prod := by sorry

end SpectrumLB
