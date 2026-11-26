-- Prove2me | Theorems.Thm_RHHeight1000_em_main_0036_0036
-- name    : RHHeight1000.em_main_0036_0036
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:38:50.665444+00:00
-- url     : https://prove2.me/theorems/bd28568d-6026-4b2f-add8-961a167c16cd
-- title:
--   A certified critical-line zero between heights 113.311 and 115.476
-- statement:
--   There exists an open interval containing a zero of the Riemann zeta function on the critical line. The first left endpoint is 113.311 and the last right endpoint is 115.476.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, https://github.com/smmercuri/zeta/tree/3dab6480a82f1bfc5de0a59550e279cf50490033 . Original T1000 bracketing data with independently checked reduced cutoffs. rows 36 through 36.

import Definitions.Def_RHT1000_Support_20261118_S003

theorem RHHeight1000.em_main_0036_0036 : Zeta.Certificates.BatchSpec 1 113311 1000 115476 1000 := by sorry
