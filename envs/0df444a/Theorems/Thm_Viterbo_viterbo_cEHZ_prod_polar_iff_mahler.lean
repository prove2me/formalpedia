-- Prove2me | Theorems.Thm_Viterbo_viterbo_cEHZ_prod_polar_iff_mahler
-- name    : Viterbo.viterbo_cEHZ_prod_polar_iff_mahler
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:19:03.417217+00:00
-- url     : https://prove2.me/theorems/53f406e7-f1a7-400c-8c2f-af3bbfd70ca4
-- title:
--   p. 3, [8] — Viterbo's conjecture for c_EHZ on K × K° (K centrally symmetric) is equivalent to Mahler's conjecture
-- statement:
--   For every $n \ge 1$, the following are equivalent:
--   - for every centrally symmetric convex body $K \subset \mathbb R^n$, $c_{\rm EHZ}(K \times K^\circ)^n \le n!\,\mathrm{Vol}(K \times K^\circ)$;
--   - (Mahler's conjecture) for every centrally symmetric convex body $K \subset \mathbb R^n$, $\mathrm{Vol}(K)\,\mathrm{Vol}(K^\circ) \ge \frac{4^n}{n!}$.
--
--   Here $K^\circ = \{p : \langle q, p\rangle \le 1 \text{ for all } q \in K\}$ and a convex body is compact with nonempty interior (`OAI.SymmetricPolar.IsSymmetricConvexBody`).
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 3, the equivalence with Mahler's conjecture, which cites Artstein-Avidan, S., Karasev, R. and Ostrover, Y., From symplectic measurements to the Mahler conjecture, Duke Math. J. 163 (2014) 2003–2022, https://doi.org/10.1215/00127094-2794999

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

open MeasureTheory
open scoped ENNReal

namespace Viterbo

theorem viterbo_cEHZ_prod_polar_iff_mahler (n : ℕ) (hn : 1 ≤ n) :
    (∀ K : Set (OAI.SymmetricPolar.Position n), OAI.SymmetricPolar.IsSymmetricConvexBody K →
        cEHZ (K ×ˢ OAI.SymmetricPolar.polar K) ^ n ≤
          (n.factorial : ℝ≥0∞) * volume (K ×ˢ OAI.SymmetricPolar.polar K)) ↔
      ∀ K : Set (OAI.SymmetricPolar.Position n), OAI.SymmetricPolar.IsSymmetricConvexBody K →
        ENNReal.ofReal (4 ^ n / n.factorial) ≤ volume K * volume (OAI.SymmetricPolar.polar K) := by
  sorry

end Viterbo
