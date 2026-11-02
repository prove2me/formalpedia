-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_d4_profile_coefficient
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.d4_profile_coefficient
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:59:05.81656+00:00
-- url     : https://prove2.me/theorems/a7a859a1-95da-4662-a3ff-105fb8b0e783
-- title:
--   Regular D4 large-ball coefficient hierarchy
-- statement:
--   Consider the regular coefficient problems obtained by equating powers in the D4 large-radius ansatz $r(z)=\rho+f(z)+g(z)/\rho+\cdots$. The leading problem is (4.19), with $f(0)=0$ and regularity at $z=1$; the next problem after that leading coefficient vanishes is
--
--   $$
--   4+(4+2z^3)g'(z)-2z(1-z^3)g''(z)=0,\qquad g(0)=0.
--   $$
--
--   The leading regular coefficient exists and is $f=0$. The next regular coefficient exists, is unique on $[0,1]$, and is
--
--   $$
--   g(z)=-\frac{\arctan((1+2z)/\sqrt3)}{\sqrt3}-\frac12\log(1+z+z^2)+\frac{\pi}{6\sqrt3},\qquad
--   g'(z)=-\frac{1+z}{1+z+z^2}.
--   $$
--
--   In the unsimplified interior expression $g'(z)=-(1+cz^2)/(1-z^3)$, regularity forces $c=-1$. In particular $g'(1)=-2/3$, using the simplified formula. Locally at zero,
--
--   $$
--   g(z)=-z+\frac{z^3}{3}-\frac{z^4}{4}+\frac{z^6}{6}-\frac{z^7}{7}+\frac{z^9}{9}+O(z^{10}).
--   $$
--
--   This is the analytic coefficient result for the formal hierarchy, including uniqueness and regular endpoint data. It does not assume an asymptotic expansion of a free surface profile, or assert convergence at $z=1$.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 20, (4.19)–(4.23)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF pp.19--20, (4.19)--(4.23): the regular coefficient hierarchy gives f=0
and the unique g on [0,1], with integration constant c=-1. The Taylor display
is only a finite local asymptotic statement, not a series equality at z=1. -/
theorem d4_profile_coefficient :
    (∃ f : ℝ → ℝ, FirstD4Coefficient f) ∧
    (∀ f : ℝ → ℝ, FirstD4Coefficient f → ∀ z ∈ Icc (0 : ℝ) 1, f z = 0) ∧
    (∃ g : ℝ → ℝ, SecondD4Coefficient g ∧
      (∀ z ∈ Icc (0 : ℝ) 1, g z = d4G z ∧ deriv g z = d4GPrime z) ∧
      (∀ c : ℝ, (∀ z ∈ Ioo (0 : ℝ) 1,
        deriv g z = -(1 + c * z ^ 2) / (1 - z ^ 3)) ↔ c = -1)) ∧
    (∀ g : ℝ → ℝ, SecondD4Coefficient g → ∀ z ∈ Icc (0 : ℝ) 1, g z = d4G z) ∧
    Asymptotics.IsBigO (nhds (0 : ℝ))
      (fun z => d4G z - (-z + z ^ 3 / 3 - z ^ 4 / 4 + z ^ 6 / 6 - z ^ 7 / 7 + z ^ 9 / 9))
      (fun z => z ^ 10) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
