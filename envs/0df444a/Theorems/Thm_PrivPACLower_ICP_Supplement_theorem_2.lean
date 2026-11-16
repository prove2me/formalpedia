-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_theorem_2
-- name    : PrivPACLower.ICP.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:10:43.068228+00:00
-- url     : https://prove2.me/theorems/fc515b56-ef54-480a-8cc7-67f783b0f3e6
-- title:
--   Theorem 2 — two-sided ICP characterization under direct-label covers and packings
-- statement:
--   Fix $0<\alpha_0\le 1/4$. Let $H$ be a non-trivial class on a domain $X$ and $\mathcal G$ a collection of hypothesis classes. Let $k\ge1$ and let $(G_1,\dots,G_k)$, $G_i\in\mathcal G$ on domains $Y_i$, each with at least two hypotheses, satisfy the conditions of Theorem 9 (fixed sets $X_i$ covering $X$ and maps $\Psi_i:X_i\to Y_i$ such that every $h\in H$ agrees on each $X_i$ with $g_i\circ\Psi_i$ for some $g_i\in G_i$), and be independently packable into $H$. Let $0<\varepsilon\le0.1$, $0\le\delta\le\alpha_0\varepsilon/64$, $0<\beta\le1/3$, $0<\alpha\le\alpha_0/(1536e)$. Then, with $c(\alpha_0)$ the constant of Theorem 1 and some $C$ depending only on $\alpha_0$,
--   $$\frac{c(\alpha_0)}{\alpha\varepsilon}\,\mathrm{ICP}_{0.1,\delta/\varepsilon}(H,\mathcal G)\ \le\ m_{\rm priv}(H;\varepsilon,\delta,\alpha,\beta)\ \le\ \frac{C}{\alpha\varepsilon}\log^2\frac{4k}{\alpha}\log\frac{2k}{\beta}\cdot\mathrm{ICP}_{0.1,\delta/\varepsilon}(H,\mathcal G).$$
--   The same two bounds hold for every general product class (Definition 6) over such a tuple, provided it is non-trivial.
--
--   The paper writes $\widetilde\Theta(\cdot)$; its proof (p. 31) takes the lower bound from Theorem 1 and the upper factor from Theorem 9 through $\sum_i s_i\le\mathrm{ICP}$, which is the displayed pair. The chosen tuple need not attain the supremum. This result shows that ICP characterizes private sample complexity, up to logarithmic factors, for classes built directly from packed components.
--
--   **Formalization Note** ICP here is the unrestricted Definition 2 (members on arbitrary domains). Costs and ICP are compared in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - reading: a distribution over an arbitrary domain X x {0,1}, with no sigma-algebra specified; privacy for every event → probability mass functions on X x {0,1}; privacy for product-measurable events of the hypothesis space (the base mission's published convention); reason: on a bare set the only sigma-algebra available is the power set, and below a real-valued measurable cardinal every probability measure on the power set is atomic, i.e. a PMF; the same convention is used in the published goal
--   - encoding: least sample size, possibly nonexistent → mpriv in Nat-infinity (sInf, infinity when no learner exists), coerced into ENNReal by costReal; reason: unlearnable classes have infinite cost; the inequalities are read in the extended nonnegative reals
--   - encoding: Theta-tilde(ICP/(alpha epsilon)) with alpha_0 fixed → lower constant lowerConstant(alpha_0) of the published goal and upper factor C/(alpha epsilon) log^2(4k/alpha) log(2k/beta) with C depending only on alpha_0, quantified before all other data; reason: the proof on p. 31 combines Theorem 1 and Theorem 9 with (12); these are exactly the hidden factors
--   - reading: ICP_{0.1,delta/epsilon}(H, G) for a collection G of hypothesis classes (Definition 2, no finiteness) → ICPAll: the supremum over packable tuples of members on arbitrary domains, without the finite-domain filter of the published ICP; reason: Definition 2 as printed; it equals the published ICP when all members have finite domains
--   - encoding: standing assumptions of Section 7.1 (k >= 1, every G_i has at least two hypotheses) and alpha <= 1/3 → hypotheses 1 <= k and AtLeastTwo (Gs i); alpha <= 1/3 follows from alpha <= alpha_0/(1536e); reason: the conditions of Theorem 9 that Theorem 2 imports
--   - encoding: "In particular, this applies to the general product class" → a second conjunct for GeneralProductClass Gs Phi with partitioning injective maps, non-trivial, members of G with at least two hypotheses; reason: states the particular case explicitly; it is an instance of the first conjunct
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 9, Theorem 2 (restated p. 31 with proof). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_PrivPACLower_ICP_Constants
import Definitions.Def_PrivPACLower_ICP_Supplement_Basics
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem theorem_2 (α₀ : ℝ) (hα₀ : 0 < α₀ ∧ α₀ ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧
      (∀ {X : Type*} (H : Set (X → Bool)) (G : ClassCollection) (k : ℕ)
        (Y : Fin k → Type) (Gs : ∀ i, Set (Y i → Bool))
        (Xs : Fin k → Set X) (Ψ : ∀ i, Xs i → Y i) (Φ : ∀ i, Y i → X),
        NontrivialClass H → 1 ≤ k → (∀ i, Gs i ∈ G (Y i)) → (∀ i, AtLeastTwo (Gs i)) →
        DirectLabelCover H Gs Xs Ψ → PackingVia H Gs Φ →
        ∀ ε δ α β : ℝ, (0 < ε ∧ ε ≤ 1/10) → (0 ≤ δ ∧ δ ≤ α₀ * ε / 64) →
          (0 < β ∧ β ≤ 1/3) → (0 < α ∧ α ≤ α₀ / (1536 * Real.exp 1)) →
          ENNReal.ofReal (lowerConstant α₀ / (α * ε)) * ICPAll α₀ (1/10) (δ / ε) H G ≤
              costReal (mpriv H ε δ α β) ∧
            costReal (mpriv H ε δ α β) ≤
              ENNReal.ofReal (C / (α * ε) * Real.log (4 * k / α) ^ 2 * Real.log (2 * k / β)) *
                ICPAll α₀ (1/10) (δ / ε) H G) ∧
      (∀ {X : Type*} (G : ClassCollection) (k : ℕ)
        (Y : Fin k → Type) (Gs : ∀ i, Set (Y i → Bool)) (Φ : ∀ i, Y i → X),
        PartitioningMaps Φ → NontrivialClass (GeneralProductClass Gs Φ) → 1 ≤ k →
        (∀ i, Gs i ∈ G (Y i)) → (∀ i, AtLeastTwo (Gs i)) →
        ∀ ε δ α β : ℝ, (0 < ε ∧ ε ≤ 1/10) → (0 ≤ δ ∧ δ ≤ α₀ * ε / 64) →
          (0 < β ∧ β ≤ 1/3) → (0 < α ∧ α ≤ α₀ / (1536 * Real.exp 1)) →
          ENNReal.ofReal (lowerConstant α₀ / (α * ε)) *
              ICPAll α₀ (1/10) (δ / ε) (GeneralProductClass Gs Φ) G ≤
              costReal (mpriv (GeneralProductClass Gs Φ) ε δ α β) ∧
            costReal (mpriv (GeneralProductClass Gs Φ) ε δ α β) ≤
              ENNReal.ofReal (C / (α * ε) * Real.log (4 * k / α) ^ 2 * Real.log (2 * k / β)) *
                ICPAll α₀ (1/10) (δ / ε) (GeneralProductClass Gs Φ) G) := by sorry

end PrivPACLower.ICP.Supplement
