-- Prove2me | Theorems.Thm_RandLatEnum_eq_7_5_area
-- name    : RandLatEnum.eq_7_5_area
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:22.249796+00:00
-- url     : https://prove2.me/theorems/f7797e79-e049-4880-aeb1-7723d21624f6
-- title:
--   Eq. (7.5) — plateau of $g_c$, flank areas $3(2c)^2/8$, $A(g_c)=c-c^2<1/8$
-- statement:
--   Let $0<c<c_{\mathrm{flat}}=(2-\sqrt2)/4$ and let $g_c$ be the ceiling of (7.5). Then:
--
--   1. the plateau has height $c$: $g_c(x)=c$ for $2c\le x\le1-2c$;
--   2. each flank has area $3(2c)^2/8$:
--   $$
--   \int_0^{2c}g_c(x)\,dx=\int_{1-2c}^{1}g_c(x)\,dx=\frac{3(2c)^2}{8};
--   $$
--   3. $A(g_c)=c(1-4c)+3c^2=c-c^2<1/8$;
--   4. there is a fixed $\varepsilon>0$ with $A(g_c+\varepsilon)<1/8$.
--
--   This is the computation that lets the area rule exclude every basis with $\max_kP_k\le cn\ln n$ for $c<c_{\mathrm{flat}}$.
--
--   Differences from the source: none.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, (7.5), p.29

import Mathlib
import Definitions.Def_RandLatEnum_cFlat
import Definitions.Def_RandLatEnum_gC
import Definitions.Def_RandLatEnum_areaA

namespace RandLatEnum

/-- **Eq. (7.5) and the area of `g_c`** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, (7.5), p.29). For
`0 < c < (2 − √2)/4`: the plateau of `g_c` has height `c` on `[2c, 1 − 2c]`; each flank has area
`3(2c)²/8`; `A(g_c) = c(1 − 4c) + 3c² = c − c² < 1/8`; and there is a fixed `ε > 0` with
`A(g_c + ε) < 1/8`. -/
theorem eq_7_5_area (c : ℝ) (hc0 : 0 < c) (hc : c < cFlat) :
    (∀ x : ℝ, 2 * c ≤ x → x ≤ 1 - 2 * c → gC c x = c) ∧
    (∫ x in (0 : ℝ)..(2 * c), gC c x) = 3 * (2 * c) ^ 2 / 8 ∧
    (∫ x in (1 - 2 * c)..(1 : ℝ), gC c x) = 3 * (2 * c) ^ 2 / 8 ∧
    areaA (gC c) = c * (1 - 4 * c) + 3 * c ^ 2 ∧
    c * (1 - 4 * c) + 3 * c ^ 2 = c - c ^ 2 ∧
    c - c ^ 2 < 1 / 8 ∧
    ∃ ε : ℝ, 0 < ε ∧ areaA (fun x => gC c x + ε) < 1 / 8 := by sorry

end RandLatEnum
