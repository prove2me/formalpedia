-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_claim_A_4
-- name    : RandomIsetThreshold.Degree.claim_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:38.791206+00:00
-- url     : https://prove2.me/theorems/797b12b7-7d6f-40e3-8d0b-e640be75ee97
-- title:
--   Claim A.4 — conditionally iid reflected path segments
-- statement:
--   Let $(G_i)_{i\ge0}$ be the stationary Bernoulli-$p$ resampling path with rate $\tau\in[0,1]$. For every integer $\ell\ge1$, the segments $X=(G_\ell,\dots,G_{2\ell})$ and $Y=(G_\ell,\dots,G_0)$ are independent and identically distributed conditional on $G_\ell$. Explicitly, for every graph $g$ and events $A,B$ of segments,
--
--   $$\Pr(G_\ell=g,X\in A,Y\in B)\Pr(G_\ell=g)=\Pr(G_\ell=g,X\in A)\Pr(G_\ell=g,Y\in B),$$
--   $$\Pr(G_\ell=g,X\in A)=\Pr(G_\ell=g,Y\in A).$$
--
--   These two identities state conditional independence and equality of conditional laws, including zero-probability atoms without division. They provide the reflection symmetry used in Lemma 4.3.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: conditional independence and identical distribution given a finite-valued graph → factorization and marginal identities multiplied by the conditioning atom probability; reason: equivalent on positive atoms; null atoms impose no conditional-law requirement
--   - generalization: the interior-bias, asymptotically chosen Section 4 path → all n,r and p,τ in [0,1]; reason: the same reversible Bernoulli replacement chain satisfies the identities also at deterministic endpoints and with empty edge sets
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 26, Claim A.4

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_ResamplingPath

open MeasureTheory
open scoped ENNReal BigOperators
universe u_claim_A_4

namespace RandomIsetThreshold.Degree

theorem claim_A_4
(n r : ℕ) (p τ : unitInterval) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    let μ := pathLaw n r p τ
    let forward := fun z : PathSample n r => fun i : Fin (ℓ + 1) => pathGraph z (ℓ + i.val)
    let backward := fun z : PathSample n r => fun i : Fin (ℓ + 1) => pathGraph z (ℓ - i.val)
    ∀ g : Cube n r,
      (∀ A B : Set (Fin (ℓ + 1) → Cube n r),
        μ.real {z | pathGraph z ℓ = g ∧ forward z ∈ A ∧ backward z ∈ B} *
          μ.real {z | pathGraph z ℓ = g} =
        μ.real {z | pathGraph z ℓ = g ∧ forward z ∈ A} *
          μ.real {z | pathGraph z ℓ = g ∧ backward z ∈ B}) ∧
      (∀ A : Set (Fin (ℓ + 1) → Cube n r),
        μ.real {z | pathGraph z ℓ = g ∧ forward z ∈ A} =
          μ.real {z | pathGraph z ℓ = g ∧ backward z ∈ A}) := by sorry

end RandomIsetThreshold.Degree
