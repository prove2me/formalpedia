-- Prove2me | Theorems.Thm_PlatformCournot_appendix_A3_decoupling
-- name    : PlatformCournot.appendix_A3_decoupling
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:02.690802+00:00
-- url     : https://prove2.me/theorems/0bc593a7-12b4-4c41-adca-43cb50db7d44
-- title:
--   Appendix A.3 — under linear costs the Nash welfare decouples across markets
-- statement:
--   Let the firms have linear costs $\bar C_i(s)=(c_i s)^+$ with $c_i\ge 0$. If $q$ is a Nash equilibrium of the open access game $(F,Q(F\times M),\pi)$ and, for every market $j$, $q^j$ is a Nash equilibrium of the game on the edge set $F\times\{j\}$, then
--
--   $$\mathrm{SW}(q,\bar C)=\sum_{j=1}^m\mathrm{SW}(q^j,\bar C).$$
--
--   With linear costs a firm's profit is a sum of per-market profits, so the networked game splits into $m$ single-market Cournot games.
--
--   Differences from the source:
--   - encoding: firms 1, …, n and markets 1, …, m → Fin n and Fin m (0-based), supply profile q i j firm first; reason: relabelling only
--   - reading: linear costs C̄ᵢ(s) = (cᵢ s)⁺ → slopes cᵢ ≥ 0; reason: the paper's costs satisfy Assumption 1 (p.8), and (c s)⁺ vanishes on (−∞, 0] only when c ≥ 0
--   - encoding: qNE(F × M) and qNE(F × {j}) → any Nash equilibria q and qʲ of the games on F × M and F × {j}; reason: Lemma 1 makes each unique
--   - encoding: SW(qNE(F × {j}),C̄) of the single-market game → SW of the m-market model at qʲ; reason: qʲ supplies nothing outside market j, so the other markets contribute 0
--   - generalization: the setting m > 1, n ≥ 2, with c₁ ≤ ⋯ ≤ c_n sorted → every n and m in ℕ, slopes unsorted; reason: the decoupling uses neither the order of the slopes nor the size of n and m; the page's range is a special case
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Appendix A.3, p.30

import Mathlib
import Definitions.Def_PlatformCournot_IsNash
import Definitions.Def_PlatformCournot_socialWelfare
import Definitions.Def_PlatformCournot_linearCost

namespace PlatformCournot

/-- **Appendix A.3: under linear costs the open access game decouples across markets.**
Pang et al., arXiv:1903.04574v3, Appendix A.3, p.30: "Given the linearity of firms' cost functions
over (0,∞), the networked Cournot game decouples across markets. Thus, the social welfare at Nash
equilibrium satisfies SW(qNE(F × M),C̄) = Σ_{j=1}^m SW(qNE(F × {j}),C̄)."

For linear costs `Cᵢ(s) = (cᵢ s)⁺` with `cᵢ ≥ 0`: if `q` is a Nash equilibrium of the open access
game and, for every market `j`, `qʲ` is a Nash equilibrium of the game on `F × {j}`, then
`SW(q) = Σⱼ SW(qʲ)`.

**Formalization Note** `F × {j}` is `Set.univ ×ˢ {j}`; `SW` is the welfare (2) of the `m`-market
model, in which `qʲ` supplies nothing outside market `j`. -/
theorem appendix_A3_decoupling {n m : ℕ} (D : AffineDemand m) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (q : Fin n → Fin m → ℝ)
    (hq : IsNash D (fun i => linearCost (c i)) Set.univ q)
    (qj : Fin m → Fin n → Fin m → ℝ)
    (hqj : ∀ j, IsNash D (fun i => linearCost (c i)) (Set.univ ×ˢ {j}) (qj j)) :
    socialWelfare D (fun i => linearCost (c i)) q =
      ∑ j, socialWelfare D (fun i => linearCost (c i)) (qj j) := by sorry

end PlatformCournot
