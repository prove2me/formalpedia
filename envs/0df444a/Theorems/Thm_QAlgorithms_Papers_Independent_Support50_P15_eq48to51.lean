-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq48to51
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq48to51
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:48:54.665839+00:00
-- url     : https://prove2.me/theorems/15325b1f-8459-4696-b794-cfa373132851
-- title:
--   eq48 51
-- statement:
--   Let $\rho_1,\ldots,\rho_m$ be a nonempty finite family of normalized $d\ge2$ dimensional states, set $S_{\min}=\min_\theta S(\rho_\theta)$, $S_{\max}=\max_\theta S(\rho_\theta)$, $a=S_{\max}-S_{\min}$, and $L=\log^2(d-1)+4$. The redundancy $R^*=\min_\sigma\max_\theta D(\rho_\theta\|\sigma)$ satisfies
--
--   $$R^*\ge\min_\sigma\max_\theta M(S(\rho_\theta)-S(\sigma),d)=\min_{S\in[0,\log d]}\max_\theta M(S(\rho_\theta)-S,d)$$
--   $$=\min_{S\in[S_{\min},S_{\max}]}\max\{M(S_{\max}-S,d),M(S_{\min}-S,d)\}$$
--   $$\ge\min_{S\in[S_{\min},S_{\max}]}\max_{\Delta\in\{S_{\max}-S,S_{\min}-S\}}\left[\frac{2\Delta^2}{L}+\frac{8\Delta^3}{3L^2}\right]\ge\frac{a^2}{2L}-\frac{a^3}{3L^2}.$$
--
--   Every displayed minimum, including the redundancy minimum, is attained in its stated domain. If Conjecture 12 holds in dimension $d$, then also $R^*\ge M(-a/2,d)$. This includes the quantum version explicitly asserted on p.15, while keeping that stronger bound conditional.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 14, eq48-51

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eqs. (48)--(51), PDF pp.14--15: all minima are attained, and the stronger bound is conditional. -/
theorem eq48to51 {d m : ℕ} (hd : 2 ≤ d) (hm : 0 < m) (a : Fin m → EntropyState d) :
    let lo := minEntropy a
    let hi := sourceEntropyMaximum a
    let q := fun s : ℝ => max (tightBound d (hi - s)) (tightBound d (lo - s))
    let p := fun s : ℝ => (max (cubicBound (easyVariance d) (hi - s))
      (cubicBound (easyVariance d) (lo - s)) : EReal)
    let v := extendedDomainInfimum (Set.Icc lo hi) q
    let u := extendedDomainInfimum (Set.Icc lo hi) p
    (∃ b : EntropyState d, (⨆ j, stateRelativeNats (a j) b) = minimaxRedundancy a) ∧
    attainsMinimum (Set.univ : Set (EntropyState d)) (fun b => entropyRadius a (entropy b.val)) ∧
    attainsMinimum (Set.Icc (0 : ℝ) (Real.log d)) (entropyRadius a) ∧
    attainsMinimum (Set.Icc lo hi) q ∧ attainsMinimum (Set.Icc lo hi) p ∧
    extendedDomainInfimum (Set.univ : Set (EntropyState d)) (fun b => entropyRadius a (entropy b.val)) ≤ minimaxRedundancy a ∧
    extendedDomainInfimum (Set.univ : Set (EntropyState d)) (fun b => entropyRadius a (entropy b.val)) =
      extendedDomainInfimum (Set.Icc (0 : ℝ) (Real.log d)) (entropyRadius a) ∧
    extendedDomainInfimum (Set.Icc (0 : ℝ) (Real.log d)) (entropyRadius a) = v ∧
    u ≤ v ∧ (redundancyBound d (hi - lo) : EReal) ≤ u ∧
    (asymmetryConjecture d → tightBound d (-(hi - lo) / 2) ≤ minimaxRedundancy a) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
