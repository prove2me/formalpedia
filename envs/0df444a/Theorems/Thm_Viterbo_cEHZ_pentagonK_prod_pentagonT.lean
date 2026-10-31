-- Prove2me | Theorems.Thm_Viterbo_cEHZ_pentagonK_prod_pentagonT
-- name    : Viterbo.cEHZ_pentagonK_prod_pentagonT
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:14:21.116993+00:00
-- url     : https://prove2.me/theorems/06305a3f-ae07-49f4-ad19-f388108e4139
-- title:
--   Proposition 1.4 — c_EHZ(K × T) = 2cos(π/10)(1 + cos(π/5)) for the pentagon K and its 90° rotation T
-- statement:
--   For the regular pentagon $K \subset \mathbb R^2_q$ with vertices $(\cos\frac{2\pi k}{5}, \sin\frac{2\pi k}{5})$ and its rotation $T \subset \mathbb R^2_p$ by $90°$, the Ekeland–Hofer–Zehnder capacity of $K \times T \subset \mathbb R^4$ is $c_{\rm EHZ}(K \times T) = 2\cos(\frac{\pi}{10})(1 + \cos(\frac{\pi}{5}))$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 4, Proposition 1.4

import Mathlib
import Definitions.Def_Viterbo

namespace Viterbo

theorem cEHZ_pentagonK_prod_pentagonT :
    cEHZ (pentagonK ×ˢ pentagonT) =
      ENNReal.ofReal (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) := by
  sorry

end Viterbo
