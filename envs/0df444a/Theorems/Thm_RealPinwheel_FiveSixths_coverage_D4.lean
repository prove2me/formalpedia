-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_coverage_D4
-- name    : RealPinwheel.FiveSixths.coverage_D4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:01:50.306195+00:00
-- url     : https://prove2.me/theorems/8e1f0268-2d65-4591-bda1-694d489181ed
-- title:
--   Four-task exact real-domain coverage
-- statement:
--   Let $d_1\ge d_2\ge d_3\ge d_4>0$ be real task densities with sum at most $5/6$. One of the sixty-nine annotated rational boxes in certificate family $W_4$ contains this vector, respecting all strict and inclusive endpoint flags:
--
--   $$\mathcal D_4\subseteq\bigcup_{w\in W_4}B_{\mathrm{annotated}}(w).$$
--
--   This is the real-domain coverage assertion. Validity of the word annotations is checked separately; no rationality hypothesis is imposed on the density vector.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and proof, printed p. 8 (PDF p. 9), Section 4 equation (3), query (4), Table 1 and Lemma 5, printed pp. 9–10 (PDF pp. 10–11), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf; D4.txt of https://github.com/grzegorz-gutowski/pinwheel_scheduling/tree/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6

import Definitions.Def_RealPinwheel_FiveSixths_CertificateD4
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.coverage_D4 (d : Fin 4 → ℝ) (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : (∑ i : Fin 4, d i) ≤ (5 : ℝ) / 6) :
    ∃ j : Fin certificateD4.size, codeBox certificateD4[j.val] d := by sorry
