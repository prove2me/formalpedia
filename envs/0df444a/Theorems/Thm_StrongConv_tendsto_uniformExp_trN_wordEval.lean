-- Prove2me | Theorems.Thm_StrongConv_tendsto_uniformExp_trN_wordEval
-- name    : StrongConv.tendsto_uniformExp_trN_wordEval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:44:18.551005+00:00
-- url     : https://prove2.me/theorems/a332a742-24bd-46f9-94b7-64af806ad30a
-- title:
--   Corollary 5.3 — weak convergence of random permutation matrices (Nica)
-- statement:
--   For every word $w$ in the letters $g_0 = e$, $g_i$, $g_{d+i} = g_i^{-1}$, the expected normalized trace $\mathbf E[\mathrm{tr}_N\, w(\boldsymbol S^N)]$ converges, as $N \to \infty$, to $\tau(w(\boldsymbol s)) = \langle \delta_e, w(\boldsymbol s)\delta_e\rangle$, as complex numbers.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 20, Corollary 5.3 (weak convergence)

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology

namespace StrongConv

theorem tendsto_uniformExp_trN_wordEval (d : ℕ) (w : List (Letter d)) :
    Tendsto (fun N : ℕ => ((uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (wordEval (sModel σ) w)) : ℝ) : ℂ))
      atTop (𝓝 (tau (wordEval (sLimit d) w))) := by
  sorry

end StrongConv
