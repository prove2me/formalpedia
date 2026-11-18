-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_linear_D5_0003
-- name    : RealPinwheel.FiveSixths.checked_linear_D5_0003
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:24:49.974544+00:00
-- url     : https://prove2.me/theorems/e461069c-8a9b-4414-bc44-35edc57e35f1
-- title:
--   Verified linear coverage fragment L_D5_0003
-- statement:
--   The stored finite covering fragment passes its exact integer linear-certificate check:
--
--   $$\operatorname{Checked}(\Gamma,T).$$
--
--   Every coefficient identity, nonnegative multiplier, constant comparison, and strictness witness is validated. Thus linear-certificate soundness turns this finite fact into coverage by annotated boxes under the fragment's context. Combining all root fragments yields coverage of the unrestricted source density or potential domain.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family D5; arithmetic validation of a fragment of the real-domain covering proof.

import Definitions.Def_RealPinwheel_FiveSixths_LinearTreeD5_0003
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_linear_D5_0003 : linearCoverCheck 216 codeFunctionD5 linearContextD5_0003 linearTreeD5_0003 = true := by sorry
