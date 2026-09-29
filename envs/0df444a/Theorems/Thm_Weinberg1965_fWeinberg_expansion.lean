-- Prove2me | Theorems.Thm_Weinberg1965_fWeinberg_expansion
-- name    : Weinberg1965.fWeinberg_expansion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:25:56.554254+00:00
-- url     : https://prove2.me/theorems/714e3f75-2c5b-45b6-ad5f-e1649651e3fe
-- title:
--   Eq. (4.9) — $f(\beta)=1+\frac{11}{6}\beta^2+\frac{63}{40}\beta^4+O(\beta^6)$
-- statement:
--   Let $f(\beta)=\dfrac{1+\beta^2}{2\beta(1-\beta^2)^{1/2}}\ln\dfrac{1+\beta}{1-\beta}$ for $0<|\beta|<1$, with $f(0)=1$ (Eq. (4.6)). Then, as $\beta\to0$,
--   $$f(\beta)=1+\frac{11}{6}\beta^2+\frac{63}{40}\beta^4+O(\beta^6).$$
--
--   This expansion is the input to the nonrelativistic evaluation of $B$ in Sec. IV: combined with the velocity expansion (4.8) of $\beta_{nm}$ and the conservation laws it produces the quadrupole formula (4.13) and the thermal gravitational-radiation estimate for the sun.
--
--   **Formalization Note** “$+\cdots$” is encoded as a big-$O$ remainder $O(\beta^6)$ as $\beta\to0$ (for real $\beta$ in a neighbourhood of $0$).
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, p. B522, Sec. IV, Eqs. (4.5)–(4.6), (4.9)

import Definitions.Def_Weinberg1965_Defs

open Asymptotics

namespace Weinberg1965

theorem fWeinberg_expansion :
    (fun β : ℝ => fWeinberg β - (1 + 11 / 6 * β ^ 2 + 63 / 40 * β ^ 4)) =O[nhds 0]
      (fun β : ℝ => β ^ 6) := by
  sorry

end Weinberg1965
