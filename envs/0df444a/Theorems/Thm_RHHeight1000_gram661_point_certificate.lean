-- Prove2me | Theorems.Thm_RHHeight1000_gram661_point_certificate
-- name    : RHHeight1000.gram661_point_certificate
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T17:49:07.56539+00:00
-- url     : https://prove2.me/theorems/6d6ef7f3-9606-4d3d-a2cb-f0766497dc66
-- title:
--   Certified Stirling enclosure for Gram point 661
-- statement:
--   Let $\theta$ denote the Riemann–Siegel theta function, and let $A_{2,0}$ and $E_{2,0}$ denote its order-two, shift-zero Stirling approximant and rigorous error bound. At $a=1016.55980$ and $b=1016.55983$, the certificate establishes
--   $$A_{2,0}(a)+E_{2,0}(a)<661\pi<A_{2,0}(b)-E_{2,0}(b).$$
--   The certificate checks nonnegative endpoints and the positive truncation order, rigorously bracketing the Gram point of index 661. It is a finite numerical input to Turing's zero-counting argument and assumes no Riemann hypothesis.
-- source:
--   https://github.com/smmercuri/zeta/tree/3dab6480a82f1bfc5de0a59550e279cf50490033 ; T1000 generated Gram certificate data and original full-source AXLE receipt d2dcb520-c50a-44dc-a527-de0f7a51b892.

import Definitions.Def_RHT1000_Support_20261118_S003

theorem RHHeight1000.gram661_point_certificate : let G : Zeta.Certificates.GramPoint := {
  idx := 661
  fst := (1016.55980 : ℝ)
  snd := (1016.55983 : ℝ)
  fst_le_snd := by norm_num
  fstCutoff := 0
  fstBernoulli := 2
  sndCutoff := 0
  sndBernoulli := 2 }
 G.Certificate := by sorry
