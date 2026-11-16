-- Prove2me | Theorems.Thm_PivotADO_OneHop_Supplement_theorem_3
-- name    : PivotADO.OneHop.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:56:52.637991+00:00
-- url     : https://prove2.me/theorems/90694f13-58a3-48d9-8205-2eb608072f7f
-- title:
--   Theorem 3 — every $(2\ell-3,2)$-hopset on some sparse graphs has size $\Omega(m^{1+1/\ell})$
-- statement:
--   Assume the standard Erdős girth conjecture. Fix an integer $\ell\ge3$. Then there are constants $a,b,\kappa>0$ such that for every threshold $N$ there are $n\ge N$ and a simple graph $G$ on $n$ vertices with $m=|E(G)|$ edges, $an\le m\le bn$, such that every $(2\ell-3,2)$-hopset $F$ for $G$ (Definition 1) satisfies
--
--   $$\kappa\,m^{1+1/\ell}\le|F|.$$
--
--   In words: under the girth conjecture there are arbitrarily large sparse graphs on which every hopset of stretch $2\ell-3$ and hopbound $2$ has size $\Omega(m^{1+1/\ell})$. The constants depend only on $\ell$, and the graph does not depend on the hopset. No degree bound is asserted: these graphs are not of constant degree.
--
--   This lower bound is polynomially superlinear and, for stretch $k>1$, stronger than what the constant-degree method gives; the paper notes it is tight by a conversion of known oracles.
--
--   Differences from the source:
--   - generalization: the standard Erdős girth conjecture (graphs of girth ≥ 2t+2 with Ω(N^{1+1/t}) edges) → for each t ≥ 1 a constant a > 0 and, for arbitrarily large N, an N-vertex graph of girth ≥ 2t+2 with ≥ a·N^{1+1/t} edges; reason: this is the weakest reading of the Ω-family, implied by every stronger reading (for every N, or for infinitely many N), so the Lean theorem has a weaker hypothesis and specializes to the source's claim; it is exactly what the proof uses (PDF p. 26)
--   - encoding: m = Θ(n) and an Ω(·) size bound, for arbitrarily large n → explicit a, b, κ > 0 chosen before the threshold N, then n ≥ N and G with a·n ≤ m ≤ b·n and κ·m^{1+1/ℓ} ≤ |F|; reason: this is the meaning of the asymptotic notation with constants depending on ℓ only
--   - encoding: a set F of edges on V → a SimpleGraph F on Fin n (unordered, loopless), size = its number of edges; reason: a loop has weight δ_G(x,x) = 0 and only spends a hop, so deleting loops keeps a hopset and lowers its size; the bound for loopless F gives the bound for all F
--   - encoding: minimum weight of a path with at most β edges → infimum in [0, ∞] over walks of length ≤ β in G ⊔ F of the sum of δ_G over the walk's edges (G-edges weigh δ_G = 1); reason: removing a cycle from a walk lowers both length and weight, so the minimum is the same; ∞ when no such walk exists
--   - encoding: stretch 2ℓ − 3 → the real number 2ℓ − 3 with natural ℓ ≥ 3; reason: no truncation, same values
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Theorem 3, p.24 (PDF p. 25); first stated p.3 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Supplement_Hopset
import Definitions.Def_PivotADO_OneHop_Supplement_ErdosGirth

set_option autoImplicit false
open scoped Classical

namespace PivotADO.OneHop.Supplement

open PivotADO.OneHop

/-- Theorem 3, Kadria–Roditty, STOC 2027 submission #584 (October 2026), p.24 (PDF 25).
All constants depend only on `ℓ` and precede `n` and `G`; the graph does not depend on the
hopset. There is no degree bound: these graphs are not of constant degree. The standard
Erdős girth conjecture is an explicit hypothesis. -/
theorem theorem_3 (hconj : ErdosGirthConjecture) :
    ∀ ℓ : ℕ, 3 ≤ ℓ → ∃ (a b κ : ℝ), 0 < a ∧ 0 < b ∧ 0 < κ ∧
      ∀ N : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        N ≤ n ∧ a * (n : ℝ) ≤ (edgeCount G : ℝ) ∧ (edgeCount G : ℝ) ≤ b * (n : ℝ) ∧
        ∀ F : SimpleGraph (Fin n), IsHopset G F (2 * (ℓ : ℝ) - 3) 2 →
          κ * (edgeCount G : ℝ) ^ (1 + 1 / (ℓ : ℝ)) ≤ (edgeCount F : ℝ) := by sorry

end PivotADO.OneHop.Supplement
