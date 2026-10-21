-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_symmetrization
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.symmetrization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:41:29.47333+00:00
-- url     : https://prove2.me/theorems/57e3790e-17f5-43ea-9de9-054028bcb0e2
-- title:
--   Rotation and permutation symmetrization without increasing error
-- statement:
--   Let $d\ge1$, $N\ge1$, $M>N$, and let $T:B((\mathbb C^d)^{\otimes M})\to B(\operatorname{Sym}^N\mathbb C^d)$ be a completely positive unital complex-linear cloning map. Use the worst-case pure-state, effect, and site error $\Delta_{\mathrm{one}}$ defined in Eq.(1). Write $R_r(u)=u^{\otimes r}$, restricted to the Bose input when $r=N$, and let $V_p$ permute the output tensor factors. Define
--   $$
--   (\tau_uT)(A)=R_N(u)^*T(R_M(u)AR_M(u)^*)R_N(u),\qquad (\tau_pT)(A)=T(V_pAV_p^*).
--   $$
--   Both actions preserve cloning maps and leave $\Delta_{\mathrm{one}}$ unchanged. For cloning maps $T,S$ and $0\le t\le1$,
--   $$
--   \Delta_{\mathrm{one}}(tT+(1-t)S)\le t\Delta_{\mathrm{one}}(T)+(1-t)\Delta_{\mathrm{one}}(S).
--   $$
--   Let $du$ be normalized Haar measure on the actual compact group $U(d)$, and set $\overline T=\int\tau_uT\,du$ and $\mathcal PT=(M!)^{-1}\sum_p\tau_pT$. Every matrix-entry integrand is integrable. The rotation average is a covariant cloning map, the permutation average is a permutation-invariant cloning map, and
--   $$
--   \Delta_{\mathrm{one}}(\overline T)\le\Delta_{\mathrm{one}}(T),\quad
--   \Delta_{\mathrm{one}}(\mathcal PT)\le\Delta_{\mathrm{one}}(T),\quad
--   \Delta_{\mathrm{one}}(\mathcal P\overline T)\le\Delta_{\mathrm{one}}(T).
--   $$
--   The last average is both covariant and permutation invariant. These reductions provide symmetric optimizers without implying symmetry of the original map.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 4, §III A, Eqs.(5)–(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF pp.3–4 Eqs.(5)–(7): exact invariances, convexity, both averages,
and joint symmetry without increasing error. Normalized Haar integrability
is concluded, not assumed as an extra restriction on arbitrary cloners. -/
theorem symmetrization (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M)
    (mu : Measure (U d)) [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu]
    (T : CloneFunction d N M) (hT : IsCloning T) :
    (∀ u : U d, IsCloning (rotateCloner u T) ∧ cloningError (rotateCloner u T) = cloningError T) ∧
    (∀ p : Equiv.Perm (Fin M),
      IsCloning (permuteCloner p T) ∧ cloningError (permuteCloner p T) = cloningError T) ∧
    (∀ S : CloneFunction d N M, IsCloning S → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      IsCloning (mixCloners t T S) ∧
      cloningError (mixCloners t T S) ≤ t * cloningError T + (1 - t) * cloningError S) ∧
    (∀ A x y, Integrable (fun u : U d => rotateCloner u T A x y) mu) ∧
    IsCloning (haarAverage mu T) ∧ IsCloningCovariant (haarAverage mu T) ∧
    cloningError (haarAverage mu T) ≤ cloningError T ∧
    IsCloning (permutationAverage T) ∧ IsPermutationInvariant (permutationAverage T) ∧
    cloningError (permutationAverage T) ≤ cloningError T ∧
    IsCloning (permutationAverage (haarAverage mu T)) ∧
    IsCloningCovariant (permutationAverage (haarAverage mu T)) ∧
    IsPermutationInvariant (permutationAverage (haarAverage mu T)) ∧
    cloningError (permutationAverage (haarAverage mu T)) ≤ cloningError T := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
