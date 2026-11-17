-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_5_3
-- name    : PolyContract.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:03:51.551379+00:00
-- url     : https://prove2.me/theorems/8c0e9305-be4c-4d5e-bc27-bb6e389dcf40
-- title:
--   Theorem 5.3 — for homogeneous costs of degree $p>1$, $\bar\alpha=1/p$ is a share bound, and it is tight
-- statement:
--   Let $p>1$. Consider a contract instance with a compact convex action set $K\subseteq\mathbb R^E_{\ge0}$ containing $0$, rewards $m\ge0$, and a cost $c:\mathbb R^E_{\ge0}\to\mathbb R_{\ge0}$ that is continuous, convex and homogeneous of degree $p$, $c(tx)=t^pc(x)$ for $t>0$. Then:
--
--   1. $\bar\alpha=1/p$ is a share bound: $\sup_{\alpha\in[0,1/p]}U_P(\alpha)=\sup_{\alpha\in[0,1]}U_P(\alpha)$;
--   2. the bound is tight: for every $p>1$ some such instance has no share bound $\bar\alpha<1/p$.
--
--   Together with Theorem 5.1 this gives $O(1+\varepsilon^{-1}\log(p/(p-1)))$ best-response calls for a $(1-\varepsilon)$-optimal contract.
--
--   Differences from the source:
--   - reading: This bound is tight → for every p > 1 some instance of the class has no share bound in [0, 1/p); reason: the proof exhibits one instance (one element, K = [0, 1], m = 1, c(x) = x^p/p) whose only optimal share is 1/p
--   - encoding: homogeneous costs of degree p > 1 (setting of §5) → compact convex K ⊆ ℝ^E_{≥0} with 0 ∈ K, m ≥ 0, c continuous, convex, nonnegative and p-homogeneous on the orthant, E nonempty; reason: the §5 setting, stated for Corollary 5.4; with c continuous and K compact the attainment assumption of §2 holds
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem 5.3, p.12 (PDF p.13); restated with proof pp.78–79 (PDF pp.79–80)

import Mathlib
import Definitions.Def_PolyContract_Supplement_GenContract

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem 5.3** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.11; restated with proof pp.78–79): for homogeneous costs of degree `p > 1`, `ᾱ = 1/p`
is a share bound. This bound is tight.

**Formalization Note** The setting is that of §5 (p.11): a compact convex action set
`K ⊆ ℝ^E_{≥0}` containing zero, rewards `m ≥ 0`, and a cost that is continuous, convex,
nonnegative and homogeneous of degree `p` on the orthant. Part one is the share bound for every such
instance; part two is tightness: for every `p > 1` some such instance has no share bound below `1/p`. -/
theorem theorem_5_3 :
    (∀ {ι : Type} [Fintype ι] (I : GenContract ι) (p : ℝ), I.Valid → IsCompact I.K → Convex ℝ I.K →
      (0 : ι → ℝ) ∈ I.K → I.IsHomogeneousCost p → I.IsShareBound (1 / p)) ∧
    (∀ p : ℝ, 1 < p → ∃ (ι : Type) (_ : Fintype ι) (I : GenContract ι), I.Valid ∧ IsCompact I.K ∧
      Convex ℝ I.K ∧ (0 : ι → ℝ) ∈ I.K ∧ I.IsHomogeneousCost p ∧
      ∀ ᾱ ∈ Set.Ico (0 : ℝ) (1 / p), ¬ I.IsShareBound ᾱ) := by sorry

end PolyContract.Supplement
