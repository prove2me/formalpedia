-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_theorem_7
-- name    : PrivPACLower.ICP.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:34.649197+00:00
-- url     : https://prove2.me/theorems/ad449155-edb3-4e20-90d5-9fb3d04e1640
-- title:
--   Theorem 7 — packing lines into linear subspaces and the subspace lower bound
-- statement:
--   Let $p$ be prime, $3\le d\le D$ and $k=\lfloor d/3\rfloor$.
--
--   1. $(\mathrm{Line}_p)^k\sqsubseteq S_{d,D}$.
--   2. Fix $\alpha_0=1/192$. There is a universal constant $c>0$ such that for all such $p,d,D$ and all $0<\varepsilon\le0.1$, $0\le\delta\le\alpha_0\varepsilon/64$, $0<\alpha\le\alpha_0/(1536e)$, $0<\beta\le1/3$, every $(\varepsilon,\delta)$-DP, $(\alpha,\beta)$-PAC learner for $S_{d,D}$, possibly improper, using $n$ examples satisfies
--   $$n\ge c\,\frac{d\min\{\log p,\log(\varepsilon/\delta)\}}{\alpha\varepsilon},$$
--   where for $\delta=0$ the minimum is $\log p$.
--
--   The paper writes $\Omega(\cdot)$. Packing lines, whose representation dimension is large, gives a bound linear in $d$ that threshold packings cannot give.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - encoding: every distribution over the finite labelled domain and every output event → PMFs over the labelled domain and product-measurable output events; reason: on a finite domain every distribution is a PMF and every set of hypotheses is measurable, so no instance changes
--   - encoding: asymptotic Omega(.) lower bound with an unspecified universal constant → an existential constant c > 0 quantified before every class, dimension, privacy, accuracy and learner parameter; reason: the paper's constants are universal (Lemma 12, Lemma 30 and Theorem 1); the order of quantifiers keeps them uniform
--   - encoding: min{log p, log(epsilon/delta)} including delta = 0 → minLogRatio (log p) epsilon delta, equal to log p when delta = 0; reason: log(epsilon/0) = +infinity; Real.log 0 = 0 is not used
--   - encoding: F_p, F_p^D and Z_p^2 → ZMod p, Fin D -> ZMod p and ZMod p x ZMod p (p prime via p.Prime); reason: the same field and vector spaces
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 26, Theorem 7 (proof p. 26). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

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


theorem theorem_7 :
    (∀ p d D : ℕ, p.Prime → 3 ≤ d → d ≤ D →
      Packable (Y := fun _ : Fin (d / 3) => ZMod p × ZMod p) (Subspaces p d D)
        (fun _ => Line p)) ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ p d D : ℕ, p.Prime → 3 ≤ d → d ≤ D →
        ∀ ε δ α β : ℝ, (0 < ε ∧ ε ≤ 1/10) → (0 ≤ δ ∧ δ ≤ (1/192) * ε / 64) →
          (0 < α ∧ α ≤ (1/192) / (1536 * Real.exp 1)) → (0 < β ∧ β ≤ 1/3) →
          ∀ (n : ℕ) (M : Learner (Fin D → ZMod p) n), IsDP M ε δ →
            IsPACLearner (Subspaces p d D) M α β →
            c * (d * minLogRatio (Real.log p) ε δ) / (α * ε) ≤ n := by sorry

end PrivPACLower.ICP.Supplement
