-- Prove2me | Theorems.Thm_RHHeight1000_gram664_point_certificate
-- name    : RHHeight1000.gram664_point_certificate
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T17:54:01.571413+00:00
-- url     : https://prove2.me/theorems/4cfaea28-9df1-4441-b411-6ca54d3aacbf
-- title:
--   Certified Stirling enclosure for Gram point 664
-- statement:
--   Let $\theta$ denote the Riemann–Siegel theta function, and let $A_{2,0}$ and $E_{2,0}$ denote its order-two, shift-zero Stirling approximant and rigorous error bound. At $a=1020.26442$ and $b=1020.26445$, the certificate establishes
--   $$A_{2,0}(a)+E_{2,0}(a)<664\pi<A_{2,0}(b)-E_{2,0}(b).$$
--   The certificate checks nonnegative endpoints and the positive truncation order, rigorously bracketing the Gram point of index 664. It is a finite numerical input to Turing's zero-counting argument and assumes no Riemann hypothesis.
-- source:
--   https://github.com/smmercuri/zeta/tree/3dab6480a82f1bfc5de0a59550e279cf50490033 ; T1000 generated Gram certificate data and original full-source AXLE receipt d2dcb520-c50a-44dc-a527-de0f7a51b892.

import Definitions.Def_RHT1000_Support_20261118_S003

theorem RHHeight1000.gram664_point_certificate : let G : Zeta.Certificates.GramPoint := {
  idx := 664
  fst := (1020.26442 : ℝ)
  snd := (1020.26445 : ℝ)
  fst_le_snd := by norm_num
  fstCutoff := 0
  fstBernoulli := 2
  sndCutoff := 0
  sndBernoulli := 2 }
 G.Certificate := by sorry
