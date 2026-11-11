-- Prove2me | Theorems.Thm_PrivPACLower_ICP_theorem_1
-- name    : PrivPACLower.ICP.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:48:23.227422+00:00
-- url     : https://prove2.me/theorems/ef94c34b-ec43-4166-bbdf-f1b6179f1899
-- title:
--   Theorem 1 — explicit ICP lower bound for private PAC learning
-- statement:
--   Fix $0<\alpha_0\le1/4$. Let $H$ be a non-trivial binary class on an arbitrary domain $X$, and let $\mathcal G$ be any collection of nonempty binary classes on finite domains. Suppose
--
--   $$0<\varepsilon\le0.1,\quad 0\le\delta\le\frac{\alpha_0\varepsilon}{64},\quad 0<\alpha\le\frac{\alpha_0}{1536e},\quad 0<\beta\le\frac13.$$
--
--   Every possibly improper randomized $(\varepsilon,\delta)$-DP, $(\alpha,\beta)$-PAC learner for $H$ using $n$ examples satisfies
--
--   $$\frac{c(\alpha_0)}{\alpha\varepsilon}\operatorname{ICP}_{0.1,\delta/\varepsilon}(H,\mathcal G)\le n.$$
--
--   The paper writes Ω(·); the proof yields the constant $c(\alpha_0)$. Explicitly, with $\bar\alpha=\alpha_0/(64e)$, $\eta=\bar\alpha/2$ and $T$ the least positive odd integer at least $72\ln(1/\eta)$,
--
--   $$c(\alpha_0)=\min\left\{\frac{\bar\alpha}{69120T},\frac{\alpha_0}{576(10\cdot101+4\alpha_0)}\right\}.$$
--
--   This is uniform over the domain, classes, collection, privacy and accuracy parameters, sample size and learner. It adds costs across every packing, not only a selected tuple. Infinite ICP rules out every finite-sample learner under these hypotheses.
--
--   **Formalization Note** The inequality is in the extended nonnegative reals. The pure privacy case $\delta=0$ is included. The learner's output is a general probability measure, and PAC failure averages both sampling and internal randomness.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - encoding: least sample size, possibly nonexistent → sInf in Nat-infinity with its infinity-preserving coercion into ENNReal; reason: unlearnable classes have infinite cost, zero-sample singleton classes retain cost zero, and infinite suprema are not replaced by zero
--   - generalization: PAC for every realizable distribution and privacy for every output event → PAC for all realizable PMFs and privacy for product-measurable events of arbitrary probability-measure outputs; reason: weakens learner hypotheses on arbitrary domains; every source learner satisfies them, and finite component domains retain all laws and events
--   - encoding: asymptotic Omega lower bound with alpha_0 fixed → the explicit constant c(alpha_0) given in the proof on pages 16–18; reason: instantiates the paper's uniform constant exactly, including its least positive odd amplification count
--   - encoding: arbitrary collection of finite-domain classes → a type-indexed collection filtered to finite domains in the ICP supremum; reason: all finite domains have small representatives; values on infinite domains are ignored
--   - encoding: standing assumption of Section 2 (p. 10) that each packed class contains at least two hypotheses → the ICP supremum also ranges over packings with singleton components; reason: a singleton class has mpriv = 0 (a zero-sample learner outputs its hypothesis), and dropping such components keeps the tuple packable, so the supremum is unchanged (the proof, Step 3 on p. 17, drops them the same way)
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 13, Theorem 1 and proof pp. 16–18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_PrivPACLower_ICP_Constants
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem theorem_1 (α₀ : ℝ) (hα₀ : 0 < α₀ ∧ α₀ ≤ 1/4)
    {X : Type*} (H : Set (X → Bool)) (hH : NontrivialClass H)
    (G : ClassCollection) (hG : ∀ (Y : Type) [Fintype Y] (C : Set (Y → Bool)), C ∈ G Y → C.Nonempty)
    (ε δ α β : ℝ) (hε : 0 < ε ∧ ε ≤ 1/10)
    (hδ : 0 ≤ δ ∧ δ ≤ α₀*ε/64)
    (hα : 0 < α ∧ α ≤ α₀/(1536*Real.exp 1)) (hβ : 0 < β ∧ β ≤ 1/3)
    (n : ℕ) (M : Learner X n) (hpriv : IsDP M ε δ) (hpac : IsPACLearner H M α β) :
    ENNReal.ofReal (lowerConstant α₀/(α*ε)) * ICP α₀ (1/10) (δ/ε) H G ≤
      (n : ℝ≥0∞) := by sorry

end PrivPACLower.ICP
