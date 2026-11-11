-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_22
-- name    : PrivPACLower.ICP.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:48:18.223197+00:00
-- url     : https://prove2.me/theorems/ed35e771-7a7b-4178-be80-dda691c6f1eb
-- title:
--   Lemma 22 — private selection among fixed hypotheses
-- statement:
--   Fix $0<\varepsilon\le1$, $0<\alpha\le1$, $0<\eta<1$, an integer $r\ge1$, and sample size $n$. There is a selection algorithm, chosen before the domain distribution and target, which for every fixed tuple $h_1,\ldots,h_r:X\to\{0,1\}$ uses exponential weights with score minus the number of sample mistakes and is $(\varepsilon,0)$-DP on every database. For any domain PMF $\mu$ and target $c$, if some $h_i$ has population error at most $\alpha/8$ and
--
--   $$n\ge\frac{24\ln(3r/\eta)}{\varepsilon\alpha},$$
--
--   then its index output $I$ on i.i.d. samples labeled by $c$ satisfies
--
--   $$\Pr[\operatorname{err}_\mu(h_I)>\alpha]\le\eta.$$
--
--   This statement keeps the algorithm independent of the unknown distribution and target and is used when comparing conditioned class costs.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - reading: a distribution on a bare set with no sigma-algebra specified → a PMF, allowing arbitrary countable support; reason: uses the brief's discrete-law interpretation; on every finite domain this includes all distributions
--   - reading: there is an (ε,0)-DP algorithm (the exponential mechanism in the proof, whose privacy holds for every database S and every h1, …, hr) → the algorithm is pinned as the exponential mechanism with score minus the number of mistakes on S and sensitivity 1, private for every hypothesis tuple; reason: the parenthetical names the mechanism of the proof on p. 37 (score −n errS(hi), sensitivity 1); the existential is witnessed by exactly that mechanism
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 37, Lemma 22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Exponential
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_22 {X : Type*} {r n : ℕ} (hr : 1 ≤ r)
    (ε α η : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (hα : 0 < α ∧ α ≤ 1)
    (hη : 0 < η ∧ η < 1) :
    ∃ A : (Fin r → X → Bool) → Mechanism (X × Bool) (Fin r) n,
      ∀ hs : Fin r → X → Bool,
        (∀ S, (A hs S : Measure (Fin r)) = exponentialLaw (selectionScore hs) ε 1 S) ∧
        IsDP (A hs) ε 0 ∧
        ∀ (μ : PMF X) (c : X → Bool),
          (∃ i, populationError (labelLaw μ c) (hs i) ≤ ENNReal.ofReal (α/8)) →
          24*Real.log (3*(r : ℝ)/η)/(ε*α) ≤ (n : ℝ) →
            selectionFailure (A hs) hs μ c α ≤ ENNReal.ofReal η := by sorry

end PrivPACLower.ICP
