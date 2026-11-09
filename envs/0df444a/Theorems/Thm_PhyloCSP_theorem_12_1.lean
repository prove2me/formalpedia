-- Prove2me | Theorems.Thm_PhyloCSP_theorem_12_1
-- name    : PhyloCSP.theorem_12_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:26:24.74353+00:00
-- url     : https://prove2.me/theorems/b95549be-25db-4199-a4a5-fd1778384344
-- title:
--   Theorem 12.1 — approximation by sampled locations
-- statement:
--   For every consistent tree transformation $F$, every integer $k\ge3$ and every integer $N\ge1$, there is a mixture $G_N$ of at most $t_k$ basic transformations, each with a template having at most $2N$ vertices, such that
--   $$
--   d_{\mathrm{TV}}\bigl(F[P],G_N[P]\bigr)\ \le\ \frac{\binom k2}{N} \tag{14}
--   $$
--   for every input pattern $P$ on at most $k$ leaves. Here $t_k$ is the number of tanglegrams on $k$ leaves.
--
--   With $N=\lceil\binom k2/\delta\rceil$ this gives Theorem 3.2(ii), with explicit bounds on the number of components and the template sizes.
--
--   Differences from the source:
--   - encoding: a mixture G_N of at most t_k basic transformations with templates of at most 2N vertices → a tree transformation G whose output law is exactly a mixture of m ≤ t_k basic transformations with templates of at most 2N vertices; reason: same object; the mixture is pinned exactly
--   - encoding: finite rooted binary trees up to label-preserving isomorphism, arbitrary leaf labels → patterns as rooted-triplet relations satisfying the axioms of Section 7.1 on finite leaf sets S ⊆ ℕ (S = ∅ included, with its single pattern); reason: the paper's own characterization (pp.1, 18); relabeling equivariance makes labels in ℕ cover every tree; the empty leaf set adds no constraint
--   - encoding: a basic transformation (Definition 3.3, steps 1–4, arbitrary ±1 child labels) → the law of the triplet relation of the output for fixed random choices (basicRawLaw), read off the output's clusters, with the child containing the least leaf labeled +1; reason: steps 2–4 determine the output's clusters; p.8 says the law does not depend on the labeling since ν is centrally symmetric
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Theorem 12.1 and eq. (14), p.41 (PDF p.43); t_k, p.40

import Mathlib
import Definitions.Def_PhyloCSP_Consistent
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_PhyloCSP_IsMixtureOfBasic
import Definitions.Def_PhyloCSP_tangle

set_option autoImplicit false

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Theorem 12.1, p.41 (PDF p.43): "For every
consistent tree transformation F, integer k ≥ 3, and integer N ≥ 1, there is a mixture GN of at
most tk basic transformations, each with a template having at most 2N vertices, such that
dTV(F[P], GN[P]) ≤ C(k, 2)/N (14) for every input pattern P on at most k leaves."

**Formalization Note.** `G` is a tree transformation whose output law is exactly a mixture of
`m ≤ t_k` basic transformations with templates of at most `2N` vertices (`IsMixtureOfBasic G m
(2 * N)`); `t_k = tangle k`; the bound holds for every leaf set of size at most `k`. `d_TV` is the published
`SamplingAC0.tvDist`, `½ Σ_ω |ρ(ω) − ρ′(ω)|` (Section 2, p.7). -/
theorem theorem_12_1 (F : TreeTransformation) (hF : Consistent F) (k : ℕ) (hk : 3 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (G : TreeTransformation) (m : ℕ), m ≤ tangle k ∧ IsMixtureOfBasic G m (2 * N) ∧
      ∀ (S : Finset ℕ), S.card ≤ k → ∀ P : Pattern ↥S,
        SamplingAC0.tvDist (F.law S P) (G.law S P) ≤ (k.choose 2 : ℝ) / N := by sorry

end PhyloCSP
