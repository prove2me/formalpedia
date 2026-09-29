-- Prove2me | Theorems.Thm_RubinSilverberg_pt_kleinCurve_ne_zero_and_five_smul
-- name    : RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/36fc0691-2fea-5d03-90c7-1bf3590535a1
-- title:
--   Rubin–Silverberg sections give 5-torsion on Klein's curve
-- statement:
--   Let $K$ be a field of characteristic zero with decidable equality, and let $u, w \in K$ satisfy $\mathrm{kleinV}(u) = u(u^{10} + 11u^{5} - 1) \neq 0$ and $w^{5} = u^{5}$. Write $H(v) = v^{20} - 228v^{15} + 494v^{10} + 228v^{5} + 1$ and $T(v) = v^{30} + 522v^{25} - 10005v^{20} - 10005v^{10} - 522v^{5} + 1$, and let $\mathrm{kleinCurve}(u)$ be the Weierstrass curve with $a_1 = a_2 = a_3 = 0$, $a_4 = -H(u)/48$, $a_6 = T(u)/864$. Let $x_0(w) = (w^{10} + 12w^{8} - 12w^{7} + 24w^{6} + 30w^{5} + 60w^{4} + 36w^{3} + 24w^{2} + 12w + 1)/12$ and $y_0(w) = (w^{13} + w^{12} + 4w^{11} + 5w^{9} + 6w^{8} + 21w^{7} + 29w^{6} + 25w^{5} + 15w^{4} + 9w^{3} + 4w^{2} + w)/2$. The assertion concerns `pt`, which returns the affine point $(x_0(w), y_0(w))$ of $\mathrm{kleinCurve}(u)$ when that pair is nonsingular on the curve and returns the point at infinity otherwise: this element of the affine point group of $\mathrm{kleinCurve}(u)$ is nonzero, and $5$ times it (as an action of $5 : \mathbb{Z}$) is zero. In particular the pair is genuinely a nonsingular point and it has order exactly $5$.
--
--   These are the explicit sections of Rubin–Silverberg's family, giving the $5$-torsion points $Q_u$ and $Q_{\zeta u}$ of Klein's curve $B_u$ whose coordinates realise a prescribed mod $5$ representation. The result feeds the independence statements [`RubinSilverberg.kleinSection_independent`](thm.html#RubinSilverberg.kleinSection_independent) and [`RubinSilverberg.rsMember_sections_independent`](thm.html#RubinSilverberg.rsMember_sections_independent), and the corresponding assertion for members of the family, [`RubinSilverberg.pt_rsMember_ne_zero_and_five_smul`](thm.html#RubinSilverberg.pt_rsMember_ne_zero_and_five_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_pt_kleinCurve_ne_zero_and_five_smul.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul {K : Type*} [Field K] [CharZero K] [DecidableEq K] (u w : K) (hV : kleinV u ≠ 0) (hw : w ^ 5 = u ^ 5) : pt (kleinCurve u) (kleinX w) (kleinY w) ≠ 0 ∧ (5 : ℤ) • pt (kleinCurve u) (kleinX w) (kleinY w) = 0 := by sorry
