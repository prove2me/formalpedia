-- Prove2me | Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_for_log_four
-- name    : TaoFivePrimes.dusart_table1_psi_bounds_for_log_four
-- status  : Open
-- author  : @abcdefg
-- created : 2026-10-14T13:00:57.439328+00:00
-- url     : https://prove2.me/theorems/8042dc39-d956-476c-a4d7-36d003a415aa
-- title:
--   Dusart Table 1: uniform psi bounds on the selected exponential ranges
-- statement:
--   Let $(b,c,\varepsilon_b)$ be any of the selected rows of Dusart's Table 1. For every real $x\ge e^b$,
--
--   $$|\psi(x)-x|\le\varepsilon_b x.$$
--
--   Here $\psi$ is the Chebyshev psi function, and $\varepsilon_b$ is the exact rational value obtained from the rounded-up entry of Table 1. The next endpoint $c$ is used only to organize interval coverage. This uniform analytic estimate supplies the table input independently of the theta transfer and logarithmic arithmetic.
-- source:
--   P. Dusart, Ramanujan J.45 (2018), Proposition 3.2, printed p.233, and Table 1, pp.234–235. https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf. Use the corrected Theorem 3.5 formula in the author’s correction dated 26 February 2018, pp.1–2: https://www.unilim.fr/pages_perso/pierre.dusart/Recherche/correctif_RJ.pdf.

import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_DusartThetaTable1Intervals

theorem TaoFivePrimes.dusart_table1_psi_bounds_for_log_four
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by sorry
