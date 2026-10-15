-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_grouped_analytic
-- name    : TaoFivePrimes.rh_high_height_dirichlet_grouped_analytic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T07:38:31.253979+00:00
-- url     : https://prove2.me/theorems/da86c667-f3c4-4839-9c6b-62b5939d3bda
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_grouped_analytic
-- statement:
--   Under uniform kernel values bounded by65537 and errors at most10^(-15), the exact50000-term normalized Dirichlet Taylor bilinear sum is enclosed by the actual929-bin integer coefficient sum with error at most10^(-12). Combines accepted all-word analytic coefficients, exact bin grouping and the accepted global weighted mass bound. No sign, winding, count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHHighDirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins

theorem TaoFivePrimes.rh_high_height_dirichlet_grouped_analytic (F G : Nat→Nat→ℂ)
    (hF:∀m:Nat,m<929 → ∀k:Nat,k<24 → ‖F m k‖≤65537)
    (heF:∀m:Nat,m<929 → ∀k:Nat,k<24 → ‖F m k-G m k‖≤1/10^15) :
 let C:Nat→Nat→ℂ:=fun n k=>
  let L:ℝ:=Real.log (n:ℝ)+Real.log Real.pi/2
  let d:ℝ:=512*L/(2*Real.pi)-(RHHighDirichletArithmetic.bin n:ℝ)
  Complex.exp (-(1/2+Complex.I*(3289999936:ℂ))*(L:ℂ))*(d:ℂ)^k
 ‖(∑n:Fin 50000,∑k:Fin 24,C (n.val+1) k.val*F (RHHighDirichletArithmetic.bin (n.val+1)) k.val)-
   (∑m:Fin 929,∑k:Fin 24,
    (RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient m.val k.val)/(2:ℂ)^128)*G m.val k.val)‖≤1/10^12 := by sorry
