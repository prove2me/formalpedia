-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_uniform_matching_contains
-- name    : QuantumBipartiteTesting.Bipartiteness.uniform_matching_contains
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:47:17.291653+00:00
-- url     : https://prove2.me/theorems/6a47f7c3-8e3b-456d-85f0-93ba592daf2f
-- title:
--   Probability that a uniform perfect matching contains prescribed disjoint pairs
-- statement:
--   Let $N$ be even and let $E$ be a set of pairwise vertex-disjoint, nonloop unordered pairs from an $N$-element set. For a uniformly chosen perfect matching $\sigma$, the probability that all prescribed pairs occur is
--
--   $$
--   \Pr[E\subseteq\sigma]=\prod_{a=0}^{|E|-1}\frac{1}{N-2a-1}.
--   $$
--
--   The empty product is one, including the empty matching on zero vertices. This finite counting formula gives the matching probabilities within each hidden block of the graph sampling construction.
--
--   **Formalization Note** Perfect matchings use the existing fixed-point-free involution type `DerandSq.PM`; probabilities are normalized finite sums.
-- source:
--   Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Appendix A.2, printed p.30, definition and probabilistic interpretation of R_d immediately before (A.2). Counting proof adapted from accepted public Prove2Me submission 27ec2b7d-adb9-48ae-aa0c-5fe28fdd5865 (BordenaveCollins.tendsto_expFix), Part C: perfect matchings containing a partial matching, Apache 2.0.

import Definitions.Def_DerandSq_PM
import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness Finset
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.uniform_matching_contains (N : ℕ) (hN : Even N) (E : Finset (Sym2 (Fin N)))
    (hloop : ∀ p ∈ E, ¬ p.IsDiag)
    (hdisj : ∀ p ∈ E, ∀ q ∈ E, (∃ x, x ∈ p ∧ x ∈ q) → p = q) :
    Average univ (fun σ : DerandSq.PM N => if ∀ a b, s(a,b) ∈ E → σ.val a = b then (1:ℝ) else 0) =
      ∏ a ∈ range E.card, ((N:ℝ)-2*a-1)⁻¹ := by sorry
