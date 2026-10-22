-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_axis_normal_form
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.axis_normal_form
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:32:50.377218+00:00
-- url     : https://prove2.me/theorems/2f5b859c-9385-4352-80e1-b15d92e19903
-- title:
--   Proposition 8.2: Tx–Ty–Tz normal form
-- statement:
--   Let $T_x=ETE^2$, $T_y=E^2TE$, $T_z=T$ and $E=HS^3\omega^3$. Every exact single-qubit Clifford+$T$ operator has a unique expression
--
--   $$
--   T_{r_1}\cdots T_{r_n}C,\qquad n\ge0,\quad r_i\in\{x,y,z\},\quad r_i\ne r_{i+1},\quad C\in\mathcal C.
--   $$
--   Its $T$-count is the actual list length $n$, and is minimal among all exact Clifford+$T$ decompositions. A single finite suffix-rewrite algorithm symbolically returns this syntax for every input of length $m$ with cost at most $B(m+1)$, for one input-independent $B>0$.
--
--   Only adjacent repetitions are forbidden; arbitrary Clifford operators occur when $n=0$.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 11, Proposition 8.2: Tx–Ty–Tz normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Proposition 8.2, PDF pp.11-12: unique axis syntax, actual rotation count,
T-optimality and a linear symbolic algorithm. The empty axis list is allowed. -/
theorem axis_normal_form :
    (∀ U : Mat, CliffordT U → ∃! M : AxisForm, axisValue M = U) ∧
    (∀ (M : AxisForm) (w : List Input), inputWordMatrix w = axisValue M →
      M.axes.length ≤ inputTCount w) ∧
    LinearNormalizer axisTokens axisValue := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
