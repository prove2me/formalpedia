-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_prop2_second_factor_pos
-- name    : PlatformEntry.Regimes.prop2_second_factor_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:41.55784+00:00
-- url     : https://prove2.me/theorems/b79ee344-6bce-4de0-a8ab-f6e55f60e67e
-- title:
--   Proof of Proposition 2, PDF p. 36 — the second factor of Num(f,β,δ) is positive under (5)
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy condition (5). Then
--
--   $$
--   \beta^4(1+f)^2 - 2\beta^3(1+f)(-1+\delta f) + 8(2+\delta-\delta^2 f) - 4\beta(2+\delta^2-\delta(3+2f)) + 2\beta^2(-6-4f-\delta f+\delta^2(-1+f^2)) > 0 .
--   $$
--
--   Together with the factorization of $\mathrm{Num}(f,\beta,\delta)$, this shows that under (5) the seller prefers entry exactly when the function (11) is positive.
--
--   **Formalization Note** Condition (5) is needed: at $(\delta,f,\beta) = (0,0,1)$, where (5) fails, the expression equals $-1$.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Proposition 2, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem prop2_second_factor_pos (δ f β : ℝ) (hbox : InBox δ f β) (h5 : cond5 δ f β) :
    0 < S2 δ f β := by sorry

end PlatformEntry.Regimes
