-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_35_1_i
-- name    : RamanujanNotebooks.entry_35_1_i
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T06:47:57.962779+00:00
-- url     : https://prove2.me/theorems/6121a4e8-5129-47b7-ac54-a14e94246bd9
-- title:
--   Closed form of the theta function φ at e^{-π} in terms of the gamma function
-- statement:
--   Let $a=\pi^{1/4}/\Gamma(3/4)$. Then $\varphi(e^{-\pi})=a$. Here $\varphi(q)=\sum_{k\in\mathbb Z}q^{k^2}$.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part V (Springer, 1998), Chapter 35, Entry 1(i), p. 325.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_thetaPhi

namespace RamanujanNotebooks
theorem entry_35_1_i :
    (thetaPhi (((Real.exp (-Real.pi)) : ℝ) : ℂ)) =
      (((((Real.pi) ^ ((1 : ℝ) / 4)) / (Real.Gamma ((3 : ℝ) / (4 : ℝ)))) : ℝ) : ℂ) := by sorry
end RamanujanNotebooks
