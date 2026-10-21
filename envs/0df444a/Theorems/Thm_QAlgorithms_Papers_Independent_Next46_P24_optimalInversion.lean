-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P24_optimalInversion
-- name    : QAlgorithms.Papers.Independent.Next46.P24.optimalInversion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:56:18.610379+00:00
-- url     : https://prove2.me/theorems/91f6fae5-fb48-4b77-aec4-bad198f0c9f5
-- title:
--   Unnumbered optimal inversion result, Eqs.(9)–(11): optimum 2/d^2 and an attaining comb
-- statement:
--   Fix an integer $d\ge2$, fixed coordinate bases on four copies of $\mathbb C^d$, and the unnormalized Choi convention. Feasible combs obey $C\succeq0$, $\operatorname{Tr}_3 C=I_2\otimes C^{(1)}$, and $\operatorname{Tr}_1 C^{(1)}=I_0$. Write $\overline F(C)=d^{-2}\int\langle v_U|C|v_U\rangle\,dU$, where $v_U=|U^\dagger\rangle\!\rangle_{30}\otimes|U^*\rangle\!\rangle_{21}$ in wire order $3210$ and $dU$ is normalized Haar measure on $SU(d)$. Let $P^\pm=(I\pm\mathrm{Swap})/2$ and $d_\pm=d(d\pm1)/2$. Then the comb
--
--   $$
--   C_{\mathrm{opt}}=\frac{P^+_{31}\otimes P^+_{20}}{d_+}+\frac{P^-_{31}\otimes P^-_{20}}{d_-}
--   =\int_{SU(d)}|v_U\rangle\langle v_U|\,dU
--   $$
--
--   is feasible and attains the global optimum:
--
--   $$
--   \overline F(C)\le\frac2{d^2}=\overline F(C_{\mathrm{opt}})\qquad\text{for every feasible }C.
--   $$
--
--   The Haar kernel and every feasible fidelity integrand are integrable. Within the invariant ansatz $C(a)=\sum_{\mu,\nu\in\{+,-\}}a^{\mu\nu}P^\mu_{31}\otimes P^\nu_{20}$ with nonnegative real coefficients and the same feasibility constraints, equality holds precisely when $a^{\mu\nu}=\delta_{\mu\nu}/d_\mu$, equivalently when $C(a)=C_{\mathrm{opt}}$. This equality characterization is confined to the invariant ansatz. The result gives the optimal average channel fidelity for inversion with one use of the unknown unitary channel.
--
--   **Formalization Note** The paper leaves $d\ge2$ implicit. At $d=1$ its printed optimum is $2$ although channel fidelity is $1$, and $d_-=0$; the statement explicitly excludes that omitted case.
-- source:
--   Minimal computational-space implementation of multi-round quantum protocols, arXiv:1006.1780v1, PDF p. 3, Unnumbered optimal inversion result, Eqs.(9)–(11): optimum 2/d^2 and an attaining comb

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P24

noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P24

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.combContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.pairContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.wireContinuousENorm

/-- PDF p.3, Eqs.(9)-(11): global upper bound, an attaining comb and its Haar formula,
with the equality characterization confined to the nonnegative invariant ansatz.
The implicit nontrivial-dimension hypothesis d >= 2 is made explicit: d=1 would
make the printed bound 2/d squared equal 2 and is a source omission. -/
theorem optimalInversion (d : ℕ) (hd : 2 ≤ d) :
    IsInversionComb (optimalComb d) ∧
    inversionAverage (optimalComb d) = 2 / (d : ℝ)^2 ∧
    Integrable (@inversionKernel d) (haar d) ∧
    optimalComb d = ∫ U, inversionKernel U ∂haar d ∧
    (∀ C : CombMatrix d, IsInversionComb C →
      Integrable (inversionFidelity C) (haar d) ∧ inversionAverage C ≤ 2 / (d : ℝ)^2) ∧
    (∀ a : Bool → Bool → ℝ, (∀ b c, 0 ≤ a b c) → IsInversionComb (invariantComb d a) →
      (inversionAverage (invariantComb d a) = 2 / (d : ℝ)^2 ↔
        ∀ b c, a b c = if b = c then (inversionSectorDimension d b)⁻¹ else 0) ∧
      (inversionAverage (invariantComb d a) = 2 / (d : ℝ)^2 ↔
        invariantComb d a = optimalComb d)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P24

end
