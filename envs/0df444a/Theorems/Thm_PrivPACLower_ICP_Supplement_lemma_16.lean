-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_lemma_16
-- name    : PrivPACLower.ICP.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:17:50.507215+00:00
-- url     : https://prove2.me/theorems/3f364732-addf-406d-a914-c7194c5b5ca8
-- title:
--   Lemma 16 (used in the proof of Theorem 9) — VC dimension and private cost of a lifted class
-- statement:
--   Fix $0<\alpha_0\le1/4$. There is a constant $C>0$ depending only on $\alpha_0$ such that for all $0<\varepsilon\le0.1$, $0\le\delta\le\alpha_0\varepsilon/64$, every class $G\subseteq\{0,1\}^Y$ with at least two hypotheses, every $X_i\subseteq X$, $\Psi_i:X_i\to Y$ and $o_i:X\setminus X_i\to\{0,1\}$, the lifted class $\widetilde G$ (equal to $g\circ\Psi_i$ on $X_i$ and to $o_i$ outside, $g\in G$) satisfies
--   $$\mathrm{VC}(\widetilde G)\le\mathrm{VC}(G)\qquad\text{and}\qquad m_{\rm priv}(\widetilde G;0.1,\delta/\varepsilon,\alpha_0,1/4)\le C\,m_{\rm priv}(G;0.1,\delta/\varepsilon,\alpha_0,1/4).$$
--
--   A private learner for a component class thus yields one for its lift to the whole domain at a constant-factor cost. The maps $\Psi_i$ need not be injective or surjective and $o_i$ is arbitrary.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - reading: a distribution over an arbitrary domain X x {0,1}, with no sigma-algebra specified; privacy for every event → probability mass functions on X x {0,1}; privacy for product-measurable events of the hypothesis space (the base mission's published convention); reason: on a bare set the only sigma-algebra available is the power set, and below a real-valued measurable cardinal every probability measure on the power set is atomic, i.e. a PMF; the same convention is used in the published goal
--   - encoding: least sample size, possibly nonexistent → mpriv in Nat-infinity (sInf, infinity when no learner exists), coerced into ENNReal by costReal; reason: unlearnable classes have infinite cost; the inequalities are read in the extended nonnegative reals
--   - encoding: standing assumptions of Section 7.1: 0 < epsilon <= 0.1, 0 <= delta <= alpha_0 epsilon/64, every G_i with at least two hypotheses, constants depending only on alpha_0 → hypotheses on epsilon and delta, AtLeastTwo G, and C quantified after alpha_0 and before everything else; reason: the section fixes these on p. 29
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 30, Lemma 16 (proof p. 46). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_PrivPACLower_ICP_Supplement_Basics
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem lemma_16 (α₀ : ℝ) (hα₀ : 0 < α₀ ∧ α₀ ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε δ : ℝ, (0 < ε ∧ ε ≤ 1/10) → (0 ≤ δ ∧ δ ≤ α₀ * ε / 64) →
        ∀ {X Y : Type*} (G : Set (Y → Bool)) (Xi : Set X) (Ψ : Xi → Y) (o : ↥(Xiᶜ) → Bool),
          AtLeastTwo G →
          UnderstandingML.vcDim (liftedClass G Xi Ψ o) ≤ UnderstandingML.vcDim G ∧
          costReal (mpriv (liftedClass G Xi Ψ o) (1/10) (δ / ε) α₀ (1/4)) ≤
            ENNReal.ofReal C * costReal (mpriv G (1/10) (δ / ε) α₀ (1/4)) := by sorry

end PrivPACLower.ICP.Supplement
