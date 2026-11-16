-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_theorem_5
-- name    : PrivPACLower.ICP.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:13:44.153337+00:00
-- url     : https://prove2.me/theorems/ee385e15-04fc-49ad-a804-bf762398a447
-- title:
--   Theorem 5 — private lower bounds for boxes, interval unions, halfspaces and polygons
-- statement:
--   Fix $\alpha_0=1/192$. There are universal constants $c_\delta>0$ (the constant of Corollary 2) and $c>0$ such that for all $0<\varepsilon\le0.1$, $0\le\delta\le\alpha_0\varepsilon/64$, $0<\alpha\le\alpha_0/(1536e)$, $0<\beta\le1/3$, every $(\varepsilon,\delta)$-DP, $(\alpha,\beta)$-PAC learner, possibly improper, using $n$ examples satisfies:
--
--   1. for $B_{N,d}$ with $N\ge3$, if $\delta\le c_\delta\varepsilon/(1+\log^*N)$: $\displaystyle n\ge c\,\frac{d(1+\log^*N)}{\alpha\varepsilon}$;
--   2. for $I_{N,k}$ with $N\ge2k$, if $\delta\le c_\delta\varepsilon/(1+\log^*(N/k))$: $\displaystyle n\ge c\,\frac{k(1+\log^*(N/k))}{\alpha\varepsilon}$;
--   3. for $H_{N,d}$ with $N\ge3$, if $\delta\le c_\delta\varepsilon/(1+\log^*N)$: $\displaystyle n\ge c\,\frac{d(1+\log^*N)}{\alpha\varepsilon}$;
--   4. for $C_{N,k}$ with $\lfloor\sqrt N\rfloor\ge2k$, if $\delta\le c_\delta\varepsilon/(1+\log^*(\sqrt N/k))$: $\displaystyle n\ge c\,\frac{k(1+\log^*(\sqrt N/k))}{\alpha\varepsilon}$.
--
--   The paper writes $\Omega(\cdot)$. These bounds are multiplicative in the dimension (or number of pieces) and the iterated logarithm of the grid size.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - encoding: every distribution over the finite labelled domain and every output event → PMFs over the labelled domain and product-measurable output events; reason: on a finite domain every distribution is a PMF and every set of hypotheses is measurable, so no instance changes
--   - encoding: asymptotic Omega(.) lower bound with an unspecified universal constant → an existential constant c > 0 quantified before every class, dimension, privacy, accuracy and learner parameter; reason: the paper's constants are universal (Corollary 2 and Theorem 1); the order of quantifiers keeps them uniform
--   - reading: "Let c_delta be the constant of Corollary 2" → an existential c_delta > 0 quantified jointly with the Omega constant before all parameters; reason: Corollary 2 only asserts that such a universal constant exists (c_delta = c/1890 with c from Theorem 4)
--   - generalization: k >= 1 (implicit in N/k and sqrt(N)/k) and d >= 1 → k = 0 and d = 0 allowed; reason: then the right-hand side is 0 (real division by zero is 0 and log* 0 = 0), so the bound holds trivially; for k, d >= 1 it is the source's claim
--   - encoding: the grid [N] = {1, ..., N} (and [N]^d, [N]^2) → Fin N with x standing for x + 1 (real coordinates (x : R) + 1 in halfspaces and halfplanes); reason: a bijective relabelling of the finite domain; no instance changes
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 23, Theorem 5 (proof pp. 23–24; Corollary 2, p. 21). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

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


theorem theorem_5 :
    ∃ cδ c : ℝ, 0 < cδ ∧ 0 < c ∧
      ∀ ε δ α β : ℝ, (0 < ε ∧ ε ≤ 1/10) → (0 ≤ δ ∧ δ ≤ (1/192) * ε / 64) →
        (0 < α ∧ α ≤ (1/192) / (1536 * Real.exp 1)) → (0 < β ∧ β ≤ 1/3) →
        (∀ N d : ℕ, 3 ≤ N → δ ≤ cδ * ε / (1 + logStar (N : ℝ)) →
          ∀ (n : ℕ) (M : Learner (Fin d → Fin N) n), IsDP M ε δ →
            IsPACLearner (Boxes N d) M α β →
            c * (d * (1 + logStar (N : ℝ))) / (α * ε) ≤ n) ∧
        (∀ N k : ℕ, 2 * k ≤ N → δ ≤ cδ * ε / (1 + logStar ((N : ℝ) / k)) →
          ∀ (n : ℕ) (M : Learner (Fin N) n), IsDP M ε δ →
            IsPACLearner (Intervals N k) M α β →
            c * (k * (1 + logStar ((N : ℝ) / k))) / (α * ε) ≤ n) ∧
        (∀ N d : ℕ, 3 ≤ N → δ ≤ cδ * ε / (1 + logStar (N : ℝ)) →
          ∀ (n : ℕ) (M : Learner (Fin d → Fin N) n), IsDP M ε δ →
            IsPACLearner (Halfspaces N d) M α β →
            c * (d * (1 + logStar (N : ℝ))) / (α * ε) ≤ n) ∧
        (∀ N k : ℕ, 2 * k ≤ Nat.sqrt N →
          δ ≤ cδ * ε / (1 + logStar (Real.sqrt N / k)) →
          ∀ (n : ℕ) (M : Learner (Fin N × Fin N) n), IsDP M ε δ →
            IsPACLearner (Polygons N k) M α β →
            c * (k * (1 + logStar (Real.sqrt N / k))) / (α * ε) ≤ n) := by sorry

end PrivPACLower.ICP.Supplement
