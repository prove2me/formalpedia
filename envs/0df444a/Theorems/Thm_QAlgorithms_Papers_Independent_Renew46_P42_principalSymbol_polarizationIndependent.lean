-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_principalSymbol_polarizationIndependent
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.principalSymbol_polarizationIndependent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:23:51.348992+00:00
-- url     : https://prove2.me/theorems/285dcc92-c9e1-4d0f-a10a-33406a914e73
-- title:
--   Lorentz-transformed scalar principal symbol for every polarization
-- statement:
--   In the frozen-coefficient nondispersive optical model let $c>0$, $n\ge1$ and $|\mathbf u|<c$. Let $\eta=\operatorname{diag}(1,-1,-1,-1)$, $U=\gamma(1,\mathbf u/c)$, $G=\eta+(n^2-1)UU^T$, $G_0=\operatorname{diag}(n^2,-1,-1,-1)$, and let $\Lambda$ be the rest-to-laboratory Lorentz boost, with identity value at zero flow. Then
--
--   $$\Lambda\eta\Lambda^T=\eta,\qquad G=\Lambda G_0\Lambda^T,\qquad (\Lambda^Tp)^TG_0(\Lambda^Tp)=p^TGp.$$
--
--   For every real covector $p$ and complex component matrix $F$, multiplication by this common symbol commutes with the field-strength change of components:
--
--   $$[(\Lambda^Tp)^TG_0(\Lambda^Tp)]\,\Lambda^TF\Lambda=\Lambda^T[(p^TGp)F]\Lambda.$$
--
--   Thus the characteristic equation is the same for every field-strength component. The statement concerns the principal part and does not identify polarization-dependent amplitude transport or exact variable-coefficient Maxwell propagation.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 4, §III A–B, (19)–(32): Lorentz-transformed principal wave equation and polarization independence

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.4, (19)–(32): Lorentz transformation of the frozen wave symbol.
The same scalar acts on every polarization component; amplitude transport is excluded. -/
theorem principalSymbol_polarizationIndependent (c n : ℝ) (u : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    lorentzBoost c u * minkowskiMetric * (lorentzBoost c u).transpose = minkowskiMetric ∧
    gUp c n u = lorentzBoost c u * gUp c n 0 * (lorentzBoost c u).transpose ∧
    (∀ p : V4,
      quadratic (gUp c n 0) (apply4 (lorentzBoost c u).transpose p) =
        quadratic (gUp c n u) p) ∧
    (∀ (p : V4) (F : Matrix (Fin 4) (Fin 4) ℂ),
      let L : Matrix (Fin 4) (Fin 4) ℂ := (lorentzBoost c u).map (fun a => (a : ℂ))
      ((quadratic (gUp c n 0) (apply4 (lorentzBoost c u).transpose p) : ℝ) : ℂ) •
          (L.transpose * F * L) =
        L.transpose * (((quadratic (gUp c n u) p : ℝ) : ℂ) • F) * L) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
