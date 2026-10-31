-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_local_conversions_and_modulus
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.local_conversions_and_modulus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:12:44.81262+00:00
-- url     : https://prove2.me/theorems/bf50023f-a0dd-4876-8f7c-c61ed797020e
-- title:
--   Eqs.(13)–(19): corrected local conversion and continuity modulus
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   Assume $E(\Phi^+)=1$. Fix a density $\rho$ and radius $\epsilon>0$ in positive finite local dimensions. Suppose the entire affine trace-one Hermitian closed trace-distance ball consists of densities, and all its densities are distillable. Set
--
--   $$B=\{\tau:T(\rho,\tau)\le\epsilon\},\quad d=\inf_{\tau\in B}E_d(\tau),\quad c=\sup_{\tau\in B}E_c(\tau),$$
--
--   and assume the uniform bounds $0<d\le c<\infty$ used in the quantitative argument. Put $r=d/c$ and $\kappa(p)=p(1-r)/(r+(1-r)p)$. For any density $\sigma$ with $T(\rho,\sigma)=\epsilon$ and $0\le p\le1$, let $\rho_p=(1-p)\rho+p\sigma$. Both asymptotic conversions $\rho\to\rho_p^{\otimes(1-\kappa(p))}$ and $\rho_p\to\rho^{\otimes(1-\kappa(p))}$ are achievable, and
--
--   $$\kappa(p)\le\frac{p(1-r)}r,\qquad |E(\rho)-E(\rho_p)|\le\frac{pc(c-d)}d.$$
--
--   Consequently, for every $\rho'\in B$,
--
--   $$|E(\rho)-E(\rho')|\le\frac{c(c-d)}{d\epsilon}T(\rho,\rho').$$
--
--   The source's printed coefficient has a sign error and lacks the factor $c/d$. The rewritten loss covers $r=1$ and $p=0$. The extrema are computed from the ball, and none of these uniform quantitative premises is imposed on the main continuity theorem.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 2, Eqs.(13)–(19): corrected local conversion and continuity modulus

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF pp.2–3 (13)–(19): local conversions and corrected modulus.
Printed: Delta=Ed(B)-Ec(B). Changed: Delta=c(c-d)/d, with d=inf_B Ed,
c=sup_B Ec. Why: kappa <= p(1-r)/r gives kappa*c <= p*c(c-d)/d.
The affine ball must consist of densities, so opposite directions exist.
No unjustified approximation of this coefficient as the centre's gap is claimed. -/
theorem local_conversions_and_modulus
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E) (hunit : resourceSingleValue E phiPlusDensity = 1)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (rho : VidalOperator a b)
    (hrho : IsDensityMatrix rho) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hball : ∀ X : AffineState a b, traceDistance rho X.val ≤ epsilon →
      IsDensityMatrix X.val)
    (hdist : ∀ X ∈ densityBall rho epsilon, 0 < loccDistillable X)
    (hyield : 0 < ballYield rho epsilon)
    (horder : ballYield rho epsilon ≤ ballCost rho epsilon) :
    let d := ballYield rho epsilon
    let c := ballCost rho epsilon
    let r := d / c
    (∀ sigma : VidalOperator a b, IsDensityMatrix sigma → traceDistance rho sigma = epsilon →
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        AsymptoticLOCCConverts (single rho 1) (single (affineMixture rho sigma p) (1-conversionLoss p r)) ∧
        AsymptoticLOCCConverts (single (affineMixture rho sigma p) 1) (single rho (1-conversionLoss p r)) ∧
        conversionLoss p r ≤ p*(1-r)/r ∧
        |resourceSingleValue E rho - resourceSingleValue E (affineMixture rho sigma p)| ≤ p*c*(c-d)/d) ∧
    (∀ rho2 ∈ densityBall rho epsilon,
      |resourceSingleValue E rho - resourceSingleValue E rho2| ≤ (c*(c-d)/(d*epsilon))*traceDistance rho rho2) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
