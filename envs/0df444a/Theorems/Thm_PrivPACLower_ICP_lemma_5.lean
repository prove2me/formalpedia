-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_5
-- name    : PrivPACLower.ICP.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:11.995357+00:00
-- url     : https://prove2.me/theorems/1860592e-76e3-4ce1-a135-e5cda57ef90f
-- title:
--   Lemma 5 — one hard distribution before the private algorithm
-- statement:
--   Let $G$ be a nonempty binary class on a finite domain $Y$, let $0<\varepsilon\le1$, $0<\alpha_0\le1/4$ and $0\le\delta\le\alpha_0/8$, and set $\bar\alpha=\alpha_0/(8e)$. For every integer $1\le q<m_{\rm priv}(G;\varepsilon,\delta,\alpha_0,1/4)$, there is a distribution $\nu$ over $G$-realizable databases of length $q$ such that
--
--   $$\forall M\text{ that is }(\varepsilon,\delta)\text{-DP},\qquad \mathbb E_{S\sim\nu,M}[\operatorname{err}_S(M(S))]>\bar\alpha.$$
--
--   The distribution is chosen before the mechanism. Since the domain and database length are finite, the PMF representation includes every possible database distribution. This uniform hardness permits independent costs to be combined.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - encoding: least sample size, possibly nonexistent → sInf in Nat-infinity with its infinity-preserving coercion into ENNReal; reason: unlearnable classes have infinite cost, zero-sample singleton classes retain cost zero, and infinite suprema are not replaced by zero
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 13, Lemma 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_5 {Y : Type*} [Fintype Y] (G : Set (Y → Bool)) (hG : G.Nonempty)
    (ε δ α₀ : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (hα₀ : 0 < α₀ ∧ α₀ ≤ 1/4)
    (hδ : 0 ≤ δ ∧ δ ≤ α₀/8) (q : ℕ) (hq : 1 ≤ q)
    (hcost : (q : ℕ∞) < mpriv G ε δ α₀ (1/4)) :
    ∃ ν : PMF (Fin q → Y × Bool),
      (∀ S, ν S ≠ 0 → RealizableDB G S) ∧
      ∀ M : Learner Y q, IsDP M ε δ →
        ENNReal.ofReal (α₀/(8*Real.exp 1)) < expectedEmpirical ν M := by sorry

end PrivPACLower.ICP
