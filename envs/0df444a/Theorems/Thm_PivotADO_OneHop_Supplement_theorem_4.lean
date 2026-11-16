-- Prove2me | Theorems.Thm_PivotADO_OneHop_Supplement_theorem_4
-- name    : PivotADO.OneHop.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:18.728209+00:00
-- url     : https://prove2.me/theorems/0db50e48-90d5-4da8-aaff-bccc2243fb3d
-- title:
--   Theorem 4 — every $(\frac{2\ell-\beta-1}{\beta-1},\beta)$-hopset on some sparse graphs has size $\Omega(m^{1+1/\ell})$
-- statement:
--   Assume the standard Erdős girth conjecture. Fix integers $\beta\ge2$ and $\ell>\beta$. Then there are constants $a,b,\kappa>0$ such that for every threshold $N$ there are $n\ge N$ and a simple graph $G$ on $n$ vertices with $m=|E(G)|$ edges, $an\le m\le bn$, such that every $\bigl(\tfrac{2\ell-\beta-1}{\beta-1},\beta\bigr)$-hopset $F$ for $G$ (Definition 1) satisfies
--
--   $$\kappa\,m^{1+1/\ell}\le|F|.$$
--
--   In words: for every fixed hopbound $\beta\ge2$, under the girth conjecture there are arbitrarily large sparse graphs on which every hopset of stretch $(2\ell-\beta-1)/(\beta-1)$ and hopbound $\beta$ has size $\Omega(m^{1+1/\ell})$. The constants depend only on $\beta$ and $\ell$, and the graph does not depend on the hopset. No degree bound is asserted.
--
--   This extends Theorem 3 (the case $\beta=2$, stretch $2\ell-3$) to every fixed hopbound.
--
--   Differences from the source:
--   - generalization: the standard Erdős girth conjecture (graphs of girth ≥ 2t+2 with Ω(N^{1+1/t}) edges) → for each t ≥ 1 a constant a > 0 and, for arbitrarily large N, an N-vertex graph of girth ≥ 2t+2 with ≥ a·N^{1+1/t} edges; reason: this is the weakest reading of the Ω-family, implied by every stronger reading (for every N, or for infinitely many N), so the Lean theorem has a weaker hypothesis and specializes to the source's claim; it is exactly what the proof uses (PDF p. 29)
--   - encoding: m = Θ(n) and an Ω(·) size bound, for arbitrarily large n → explicit a, b, κ > 0 chosen before the threshold N, then n ≥ N and G with a·n ≤ m ≤ b·n and κ·m^{1+1/ℓ} ≤ |F|; reason: this is the meaning of the asymptotic notation with constants depending on β and ℓ only
--   - encoding: a set F of edges on V → a SimpleGraph F on Fin n (unordered, loopless), size = its number of edges; reason: a loop has weight δ_G(x,x) = 0 and only spends a hop, so deleting loops keeps a hopset and lowers its size; the bound for loopless F gives the bound for all F
--   - encoding: minimum weight of a path with at most β edges → infimum in [0, ∞] over walks of length ≤ β in G ⊔ F of the sum of δ_G over the walk's edges (G-edges weigh δ_G = 1); reason: removing a cycle from a walk lowers both length and weight, so the minimum is the same; ∞ when no such walk exists
--   - encoding: stretch (2ℓ − β − 1)/(β − 1) → the real quotient (2ℓ − β − 1)/(β − 1) with natural β ≥ 2, ℓ > β; reason: computed in ℝ, so no truncated subtraction or integer division; the denominator is positive
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Theorem 4, p.27 (PDF p. 28); first stated p.4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Supplement_Hopset
import Definitions.Def_PivotADO_OneHop_Supplement_ErdosGirth

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop.Supplement

open PivotADO.OneHop

/-- Theorem 4, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.27 (PDF 28).
The stretch `(2ℓ − β − 1)/(β − 1)` is a real quotient (`β ≥ 2`, so the denominator is
positive). All constants depend only on `β` and `ℓ` and precede `n` and `G`; the graph does
not depend on the hopset. No degree bound. The standard Erdős girth conjecture is an
explicit hypothesis. -/
theorem theorem_4 (hconj : ErdosGirthConjecture) :
    ∀ β ℓ : ℕ, 2 ≤ β → β < ℓ → ∃ (a b κ : ℝ), 0 < a ∧ 0 < b ∧ 0 < κ ∧
      ∀ N : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        N ≤ n ∧ a * (n : ℝ) ≤ (edgeCount G : ℝ) ∧ (edgeCount G : ℝ) ≤ b * (n : ℝ) ∧
        ∀ F : SimpleGraph (Fin n),
          IsHopset G F ((2 * (ℓ : ℝ) - β - 1) / ((β : ℝ) - 1)) β →
            κ * (edgeCount G : ℝ) ^ (1 + 1 / (ℓ : ℝ)) ≤ (edgeCount F : ℝ) := by sorry

end PivotADO.OneHop.Supplement
