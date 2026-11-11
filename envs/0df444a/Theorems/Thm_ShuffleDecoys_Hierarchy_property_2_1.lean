-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_property_2_1
-- name    : ShuffleDecoys.Hierarchy.property_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:16.686528+00:00
-- url     : https://prove2.me/theorems/99b920ec-919e-4d7c-91a1-1ae27a433b2e
-- title:
--   Property 2.1 — canonical shuffling: dM_n/dQ^{⊗n}(z) = (1/n)Σ r(z_i), and the posteriors of the genuine position K and of Y₁
-- statement:
--   Consider the canonical shuffle-only model: $Y_1\sim P$ is shuffled with $n-1$ i.i.d. samples from $Q$, jointly independent of $Y_1$, where $P,Q$ are discrete distributions with $P\ll Q$. Let $r(y)=P(y)/Q(y)$ for $y\in\operatorname{supp}(Q)$, let $M_n=\mathrm{Law}(Z)$ be the law of the shuffled output and $K$ the position of $Y_1$ in $Z$. Then
--   $$\frac{dM_n}{dQ^{\otimes n}}(z)=L(z):=\frac1n\sum_{i=1}^nr(z_i),$$
--   and for every output $z=(z_1,\dots,z_n)$ of positive probability
--   $$\Pr[K=k\mid Z=z]=\frac{r(z_k)}{\sum_{i=1}^nr(z_i)},\qquad \Pr[Y_1=y\mid Z=z]=\sum_{k=1}^n\Pr[K=k\mid Z=z]\,\mathbf 1[z_k=y].$$
--
--   Differences from the source:
--   - encoding: the Radon–Nikodym derivative $dM_n/dQ^{\otimes n}=L$ → the mass identity $M_n(z)=\big(\prod_iQ(z_i)\big)L(z)$ for every $z$; reason: for discrete laws this is what the density statement says (and it is the full identity, including outputs off $\operatorname{supp}Q^{\otimes n}$, where both sides vanish).
--   - encoding: conditional probabilities → ratios $\Pr[A\cap\{Z=z\}]/\Pr[Z=z]$ under the law of $(Y_1,H,\sigma)$ (`shuffleExperiment`), $K=\sigma^{-1}(\text{genuine slot})$; reason: the elementary definition, at outputs of positive probability.
--   - encoding: $r$ on $\operatorname{supp}(Q)$ → $r(y)=P(y)/Q(y)$ on all of $Y$ (Lean's value $0$ off the support); reason: every $r(z_i)$ that is used at a positive-probability output has $Q(z_i)>0$; in the density identity an off-support $z_i$ makes $\prod_iQ(z_i)=0$.
--   - encoding: discrete distributions → `PMF` on an arbitrary type with decidable equality; positions $1,\dots,n$ → `Fin n` with $n\ge1$; reason: Lean conventions; $n\ge1$ excludes only the empty release.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 14, Property 2.1

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Property 2.1: in the canonical model (`Y₁ ∼ P` shuffled with `n − 1` i.i.d. draws from `Q`,
`P ≪ Q`, `r = P/Q`), the release law `Mₙ` has density `L(z) = (1/n) Σᵢ r(zᵢ)` with respect to
`Q^{⊗n}`, and for every output `z` of positive probability the posteriors of the genuine
position `K` and of `Y₁` are `r(z_k)/Σᵢ r(zᵢ)` and `Σ_k Pr[K = k | Z = z] 1[z_k = y]`. -/
theorem property_2_1 {Y : Type*} [DecidableEq Y] (n : ℕ) (hn : 1 ≤ n) (P Q : PMF Y)
    (hPQ : ∀ y, Q y = 0 → P y = 0) (R : DecoyKernel Y n) (hR : ∀ m h, R m h = ∏ i, Q (h i)) :
    let r : Y → ℝ := fun y => (P y).toReal / (Q y).toReal
    let E := shuffleExperiment P R
    let Mn : PMF (Fin n → Y) := E.map shuffleOutput
    (∀ z : Fin n → Y,
      (Mn z).toReal = (∏ i, (Q (z i)).toReal) * ((1 / (n : ℝ)) * ∑ i, r (z i))) ∧
    (∀ z : Fin n → Y, Mn z ≠ 0 → ∀ k : Fin n,
      (E.toOuterMeasure {ω | genuinePosition hn ω = k ∧ shuffleOutput ω = z}).toReal /
          (Mn z).toReal = r (z k) / ∑ i, r (z i)) ∧
    (∀ z : Fin n → Y, Mn z ≠ 0 → ∀ y : Y,
      (E.toOuterMeasure {ω | ω.1 = y ∧ shuffleOutput ω = z}).toReal / (Mn z).toReal =
        ∑ k : Fin n,
          (E.toOuterMeasure {ω | genuinePosition hn ω = k ∧ shuffleOutput ω = z}).toReal /
            (Mn z).toReal * (if z k = y then 1 else 0)) := by sorry

end ShuffleDecoys.Hierarchy
