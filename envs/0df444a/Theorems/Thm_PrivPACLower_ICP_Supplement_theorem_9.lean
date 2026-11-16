-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_theorem_9
-- name    : PrivPACLower.ICP.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:18:15.758702+00:00
-- url     : https://prove2.me/theorems/933ae4f1-1c25-4e9f-b42a-5b063f71e294
-- title:
--   Theorem 9 — private upper bound for direct-label coverings and general product classes
-- statement:
--   Fix $0<\alpha_0\le1/4$. There is a constant $C>0$ depending only on $\alpha_0$ such that the following holds. Let $k\ge1$, $G_i\subseteq\{0,1\}^{Y_i}$ for $i\in[k]$, each with at least two hypotheses, and $H\subseteq\{0,1\}^X$. Suppose fixed sets $X_i\subseteq X$ cover $X$ (they may overlap) and fix maps $\Psi_i:X_i\to Y_i$ such that for every $h\in H$ one can choose $g_i\in G_i$ with $h(x)=g_i(\Psi_i(x))$ for all $x\in X_i$ and all $i$. Then for all $0<\varepsilon\le0.1$, $0\le\delta\le\alpha_0\varepsilon/64$, $0<\alpha,\beta\le1/3$, with $s_i=m_{\rm priv}(G_i;0.1,\delta/\varepsilon,\alpha_0,1/4)$,
--   $$m_{\rm priv}(H;\varepsilon,\delta,\alpha,\beta)\le C\,\frac{\sum_{i=1}^k s_i}{\alpha\varepsilon}\log^2\frac{4k}{\alpha}\log\frac{2k}{\beta}.$$
--   In particular this holds for the general product class of Definition 6.
--
--   No packing, partition or finiteness of the domains is assumed. Together with Theorem 1 this yields Theorem 2.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - reading: a distribution over an arbitrary domain X x {0,1}, with no sigma-algebra specified; privacy for every event → probability mass functions on X x {0,1}; privacy for product-measurable events of the hypothesis space (the base mission's published convention); reason: on a bare set the only sigma-algebra available is the power set, and below a real-valued measurable cardinal every probability measure on the power set is atomic, i.e. a PMF; the same convention is used in the published goal
--   - encoding: least sample size, possibly nonexistent → mpriv in Nat-infinity (sInf, infinity when no learner exists), coerced into ENNReal by costReal; reason: unlearnable classes have infinite cost; the inequalities are read in the extended nonnegative reals
--   - encoding: standing assumptions of Section 7.1 (ranges of epsilon, delta, alpha, beta; G_i with at least two hypotheses; C depending only on alpha_0) → explicit hypotheses and C quantified after alpha_0 and before all other data; reason: fixed on p. 29
--   - encoding: "In particular, this holds for the general product class in Definition 6" → a second conjunct for GeneralProductClass Gs Phi with injective maps whose images partition X; reason: states the particular case explicitly; it is an instance of the first conjunct
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 30, Theorem 9 (proof pp. 30–31). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_PrivPACLower_ICP_Supplement_Basics
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem theorem_9 (α₀ : ℝ) (hα₀ : 0 < α₀ ∧ α₀ ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧
      (∀ {X : Type*} (k : ℕ) (Y : Fin k → Type*) (Gs : ∀ i, Set (Y i → Bool))
        (H : Set (X → Bool)) (Xs : Fin k → Set X) (Ψ : ∀ i, Xs i → Y i),
        1 ≤ k → (∀ i, AtLeastTwo (Gs i)) → DirectLabelCover H Gs Xs Ψ →
        ∀ ε δ α β : ℝ, (0 < ε ∧ ε ≤ 1/10) → (0 ≤ δ ∧ δ ≤ α₀ * ε / 64) →
          (0 < α ∧ α ≤ 1/3) → (0 < β ∧ β ≤ 1/3) →
          costReal (mpriv H ε δ α β) ≤
            ENNReal.ofReal (C / (α * ε) * Real.log (4 * k / α) ^ 2 * Real.log (2 * k / β)) *
              ∑ i, costReal (mpriv (Gs i) (1/10) (δ / ε) α₀ (1/4))) ∧
      (∀ {X : Type*} (k : ℕ) (Y : Fin k → Type*) (Gs : ∀ i, Set (Y i → Bool))
        (Φ : ∀ i, Y i → X),
        1 ≤ k → (∀ i, AtLeastTwo (Gs i)) → PartitioningMaps Φ →
        ∀ ε δ α β : ℝ, (0 < ε ∧ ε ≤ 1/10) → (0 ≤ δ ∧ δ ≤ α₀ * ε / 64) →
          (0 < α ∧ α ≤ 1/3) → (0 < β ∧ β ≤ 1/3) →
          costReal (mpriv (GeneralProductClass Gs Φ) ε δ α β) ≤
            ENNReal.ofReal (C / (α * ε) * Real.log (4 * k / α) ^ 2 * Real.log (2 * k / β)) *
              ∑ i, costReal (mpriv (Gs i) (1/10) (δ / ε) α₀ (1/4))) := by sorry

end PrivPACLower.ICP.Supplement
