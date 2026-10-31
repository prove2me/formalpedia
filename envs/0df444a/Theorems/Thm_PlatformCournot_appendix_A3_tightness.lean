-- Prove2me | Theorems.Thm_PlatformCournot_appendix_A3_tightness
-- name    : PlatformCournot.appendix_A3_tightness
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:54.526668+00:00
-- url     : https://prove2.me/theorems/c1dda54d-bfa7-4d75-85ce-c146596a583c
-- title:
--   Appendix A.3 — $\bar C^*$ attains $\rho=\frac32(1-\frac1{3n+6})$ when $\alpha_1=\dots=\alpha_m$
-- statement:
--   Let $n\ge 1$ and $m\ge 1$, let all markets have the same maximal willingness to pay, $\alpha_1=\dots=\alpha_m=a$, and let $0\le c_1<a$. Let $\bar C^*$ be the linear cost profile with slope $c_1$ for firm 1 and $c^*_i=a-\frac{2n+3}{3n+5}(a-c_1)$ for firms $i=2,\dots,n$. Then $\bar C^*$ satisfies Assumption 1, the open access game under $\bar C^*$ has a Nash equilibrium, and every Nash equilibrium $q$ of it has
--
--   $$\rho(F\times M,\bar C^*)=\frac32\Bigl(1-\frac{1}{3n+6}\Bigr).$$
--
--   This is the witness for the tightness clause of Theorem 1.
--
--   Differences from the source:
--   - encoding: firms 1, …, n and markets 1, …, m → Fin n and Fin m (0-based), supply profile q i j firm first; reason: relabelling only
--   - encoding: the unique Nash equilibrium q^NE → every Nash equilibrium q; reason: Lemma 1 makes the equilibrium unique, so a claim about every equilibrium is the claim about q^NE
--   - encoding: ρ as a real ratio with ρ := 1 when both welfares are 0 → poa in ℝ≥0∞ (x/0 = ⊤ for x > 0) and the real bound embedded by ENNReal.ofReal; reason: same values wherever the paper's ratio is defined, and no real-division junk value
--   - generalization: n ≥ 2 (the page's range in A.3) → n ≥ 1; reason: for n = 1, C̄* is the single cost (c₁ s)⁺ and ρ = 4/3 = (3/2)(1 − 1/9); the n ≥ 2 statement is a special case
--   - reading: m markets, c₁ < α₁ without loss of generality → m ≥ 1 and 0 ≤ c₁ < a; reason: for m = 0 both welfares vanish and ρ = 1; c₁ ≥ 0 because the paper's costs satisfy Assumption 1
--   - reading: "achieved by the cost function profile C̄∗" → also asserts that C̄∗ satisfies Assumption 1 and that its open access game has a Nash equilibrium; reason: C̄∗ must be one of the paper's cost function profiles (its slopes are ≥ c₁ ≥ 0), and ρ is evaluated at the game's equilibrium, which the page takes from Lemma 1
--   - generalization: the setting m > 1 of p.30 → every m ≥ 1; reason: m = 1 is the case on p.29, and the page's range is a special case
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Appendix A.3, p.30 (C̄* defined on p.29)

import Mathlib
import Definitions.Def_PlatformCournot_Assumption1
import Definitions.Def_PlatformCournot_IsNash
import Definitions.Def_PlatformCournot_poa
import Definitions.Def_PlatformCournot_poaBound
import Definitions.Def_PlatformCournot_linearCost
import Definitions.Def_PlatformCournot_worstSlope

namespace PlatformCournot

/-- **Appendix A.3: `C̄*` attains the bound when all markets share one willingness to pay.**
Pang et al., arXiv:1903.04574v3, Appendix A.3, p.30: "Additionally, it is straightforward to check
that this price of anarchy bound is achieved by the cost function profile C̄∗ if α1 = α2 = ··· = αm."

For `n ≥ 1` firms, `m ≥ 1` markets with common intercept `αⱼ = a`, and `0 ≤ c₁ < a`, the profile
`C̄*` (slopes `worstSlope n a c₁`) satisfies Assumption 1, its open access game has a Nash
equilibrium, and every Nash equilibrium of it has `ρ = (3/2)(1 − 1/(3n+6))`.

**Formalization Note** `ρ` is `poa` in `ℝ≥0∞`; the paper's firm 1 is index `0`. The page argues
`n ≥ 2`; for `n = 1`, `C̄*` is the single linear cost `(c₁ s)⁺`. -/
theorem appendix_A3_tightness {n m : ℕ} (D : AffineDemand m) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (a : ℝ) (ha : ∀ j, D.α j = a) (c₁ : ℝ) (hc₁ : 0 ≤ c₁) (hlt : c₁ < a) :
    Assumption1 (fun i => linearCost (worstSlope n a c₁ i)) ∧
      (∃ q, IsNash D (fun i => linearCost (worstSlope n a c₁ i)) Set.univ q) ∧
      ∀ q, IsNash D (fun i => linearCost (worstSlope n a c₁ i)) Set.univ q →
        poa D (fun i => linearCost (worstSlope n a c₁ i)) q = ENNReal.ofReal (poaBound n) := by sorry

end PlatformCournot
