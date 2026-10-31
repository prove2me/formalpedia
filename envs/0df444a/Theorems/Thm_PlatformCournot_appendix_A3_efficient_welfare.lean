-- Prove2me | Theorems.Thm_PlatformCournot_appendix_A3_efficient_welfare
-- name    : PlatformCournot.appendix_A3_efficient_welfare
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:52.36701+00:00
-- url     : https://prove2.me/theorems/f141472b-5646-4771-9107-2555514c3c58
-- title:
--   Appendix A.3 — efficient welfare under linear costs is $\sum_j ((\alpha_j-c_1)^+)^2/(2\beta_j)$
-- statement:
--   Let $n\ge 1$ and let the firms have linear costs $\bar C_i(s)=(c_i s)^+$ with slopes $c_i\ge 0$; let $c_{\min}=\min_i c_i$ (the paper's $c_1$ after sorting $c_1\le\dots\le c_n$). Then the efficient social welfare of open access is
--
--   $$\mathrm{SW}^*(F\times M,\bar C)=\sum_{j=1}^m\frac{\bigl((\alpha_j-c_{\min})^+\bigr)^2}{2\beta_j}.$$
--
--   In each market all efficient production comes from a cheapest firm; this is the numerator of the price of anarchy in the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: firms 1, …, n and markets 1, …, m → Fin n and Fin m (0-based), supply profile q i j firm first; reason: relabelling only
--   - generalization: c₁ ≤ ⋯ ≤ c_n sorted without loss of generality, and c₁ → the minimum slope ⨅ i, c i of an unsorted profile; reason: for a sorted profile the minimum is c₁, so the statement specializes to the page's
--   - reading: linear costs C̄ᵢ(s) = (cᵢ s)⁺ → slopes cᵢ ≥ 0; reason: the paper's costs satisfy Assumption 1 (p.8), and (c s)⁺ vanishes on (−∞, 0] only when c ≥ 0
--   - reading: n firms, c₁ the smallest slope → n ≥ 1; reason: c₁ exists only if there is a firm
--   - encoding: x⁺ → max x 0, and min over firms → ⨅ i, c i (real infimum over the finite nonempty Fin n, attained); reason: same value for n ≥ 1
--   - generalization: the setting m > 1 and n ≥ 2 of p.30 ("we restrict ourselves to n ≥ 2") → every m in ℕ and every n ≥ 1; reason: the same identity holds there; m = 1 is the display on p.29, at m = 0 both sides are 0, and the page's range is a special case
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Appendix A.3, p.30 (and p.29 for m = 1)

import Mathlib
import Definitions.Def_PlatformCournot_efficientWelfare
import Definitions.Def_PlatformCournot_linearCost

namespace PlatformCournot

/-- **Appendix A.3: efficient welfare under a linear cost profile.**
Pang et al., arXiv:1903.04574v3, Appendix A.3, p.30: "The efficient social welfare associated with
a linear cost function profile C̄ is given by SW∗(F × M,C̄) = Σ_{j=1}^m ((αj − c1)^+)² / (2βj)."
(p.29: "Ci(si) = (cisi)+ … where we assume without loss of generality that c1 ≤ ··· ≤ cn.")

For `n ≥ 1` firms with linear costs `Cᵢ(s) = (cᵢ s)⁺`, `cᵢ ≥ 0`, the efficient welfare of the
complete edge set is `Σⱼ ((αⱼ − c_min)⁺)² / (2βⱼ)`, where `c_min = minᵢ cᵢ`.

**Formalization Note** The paper's `c₁` after sorting is the minimum slope `⨅ i, c i` (a real
infimum over the finite nonempty `Fin n`, hence attained). `x⁺` is `max x 0`. -/
theorem appendix_A3_efficient_welfare {n m : ℕ} (D : AffineDemand m) (hn : 1 ≤ n)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    efficientWelfare D (fun i => linearCost (c i)) Set.univ =
      ∑ j, (max (D.α j - ⨅ i, c i) 0) ^ 2 / (2 * D.β j) := by sorry

end PlatformCournot
