-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_wdw_wkb
-- name    : WheelerDeWittSuperspace.wdw_wkb
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T22:30:20.137264+00:00
-- url     : https://prove2.me/theorems/d9572b15-e263-408f-8ff0-4ba48c5fb74e
-- title:
--   Semiclassical limit: WKB phase obeys the Einstein–Hamilton–Jacobi equation
-- statement:
--   Let $\hbar\neq0$, let $S$ be a real $C^2$ function on configuration space and $R$ any supplied potential. At every site,
--   $$\widehat{\mathcal H}\,e^{iS/\hbar}=e^{iS/\hbar}\Big(2\kappa\,G_{abcd}\,\partial_{ab}S\,\partial_{cd}S-\frac{\sqrt{\det h}}{2\kappa}(R-2\Lambda)\;-\;i\hbar\,2\kappa\,G_{abcd}\,\partial_{ab}\partial_{cd}S\Big),$$
--   where $\widehat{\mathcal H}=-2\kappa\hbar^2G_{abcd}\partial_{ab}\partial_{cd}-\tfrac{\sqrt{\det h}}{2\kappa}(R-2\Lambda)$ with the supermetric to the left. The $\hbar$-independent part is the Einstein–Hamilton–Jacobi functional.
-- source:
--   C. Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009) 877-901, https://arxiv.org/abs/0812.0295, Section 3.1 eq. (10) and Section 3.2 eq. (11); A. Peres, Nuovo Cimento 26 (1962) 53-62, https://doi.org/10.1007/BF02754342

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Milestone 5 (semiclassical limit): for `Ψ = exp(iS/hbar)`, the Wheeler–DeWitt operator is
`exp(iS/hbar)` times the Einstein–Hamilton–Jacobi functional of `S`, plus an explicit
first-order correction in `hbar`. -/
theorem wdw_wkb {X : Type*} [Fintype X] [DecidableEq X] (kappa hbar Lam : ℝ) (hkappa : kappa ≠ 0)
    (hhbar : hbar ≠ 0)
    (R : Config X → X → ℝ) (S : Config X → ℝ) (hS : ContDiff ℝ 2 S)
    (h : Config X) (x : X) :
    wdw kappa hbar Lam R (fun h' => Complex.exp (Complex.I * (S h' : ℂ) / (hbar : ℂ))) h x =
      Complex.exp (Complex.I * (S h : ℂ) / (hbar : ℂ)) *
        ((hamiltonJacobi kappa Lam R S h x : ℂ) -
          Complex.I * (hbar : ℂ) * (2 * (kappa : ℂ)) *
            ∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
              (partialR (partialR S x c d) x a b h : ℂ)) := by sorry

end WheelerDeWittSuperspace
