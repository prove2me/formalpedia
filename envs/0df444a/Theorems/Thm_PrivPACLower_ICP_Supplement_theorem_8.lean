-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_theorem_8
-- name    : PrivPACLower.ICP.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:16:54.797271+00:00
-- url     : https://prove2.me/theorems/4e416ec6-c010-4c4c-89d1-8daf1e5dda3c
-- title:
--   Theorem 8 — private lower bound for unions of paths
-- statement:
--   Fix $\alpha_0=1/192$. There is a universal constant $c>0$ such that for all $k\ge1$, $1\le d\le2^k$, $0<\varepsilon\le0.1$, $0\le\delta\le\alpha_0\varepsilon/64$, $0<\alpha\le\alpha_0/(1536e)$, $0<\beta\le1/3$, every $(\varepsilon,\delta)$-DP, $(\alpha,\beta)$-PAC learner for $T_{d,k}$, possibly improper, using $n$ examples satisfies
--   $$n\ge c\,\frac{d\min\{k,\log(\varepsilon/\delta)\}}{\alpha\varepsilon},$$
--   where for $\delta=0$ the minimum is $k$.
--
--   The paper writes $\Omega(\cdot)$. Packing paths replaces $\min\{dk,\log(\varepsilon/\delta)\}$ of the whole-class bound by $d\min\{k,\log(\varepsilon/\delta)\}$.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - encoding: every distribution over the finite labelled domain and every output event → PMFs over the labelled domain and product-measurable output events; reason: on a finite domain every distribution is a PMF and every set of hypotheses is measurable, so no instance changes
--   - encoding: asymptotic Omega(.) lower bound with an unspecified universal constant → an existential constant c > 0 quantified before every class, dimension, privacy, accuracy and learner parameter; reason: the paper's constants are universal (Lemma 12, Lemma 30 and Theorem 1); the order of quantifiers keeps them uniform
--   - encoding: min{k, log(epsilon/delta)} including delta = 0 → minLogRatio k epsilon delta, equal to k when delta = 0; reason: log(epsilon/0) = +infinity
--   - encoding: d <= 2^k with T_{d,k} defined for 1 <= d <= 2^k (p. 27) → hypotheses 1 <= d and d <= 2^k; reason: the range on which the source defines T_{d,k}
--   - encoding: the tree nodes X_{2k} (binary strings of length <= 2k) with the prefix order → TreeNodes (2k) = lists of Booleans of length <= 2k with the list prefix relation; reason: the same nodes and order
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 28, Theorem 8 (proof p. 28). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_PrivPACLower_ICP_Supplement_Classes
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem theorem_8 :
    ∃ c : ℝ, 0 < c ∧
      ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → d ≤ 2 ^ k →
        ∀ ε δ α β : ℝ, (0 < ε ∧ ε ≤ 1/10) → (0 ≤ δ ∧ δ ≤ (1/192) * ε / 64) →
          (0 < α ∧ α ≤ (1/192) / (1536 * Real.exp 1)) → (0 < β ∧ β ≤ 1/3) →
          ∀ (n : ℕ) (M : Learner (TreeNodes (2 * k)) n), IsDP M ε δ →
            IsPACLearner (PathUnion d k) M α β →
            c * (d * minLogRatio k ε δ) / (α * ε) ≤ n := by sorry

end PrivPACLower.ICP.Supplement
