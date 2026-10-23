-- Prove2me | Theorems.Thm_RobustOpt2009_Bernstein_proposition_4_2_3
-- name    : RobustOpt2009.Bernstein.proposition_4_2_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:24.400902+00:00
-- url     : https://prove2.me/theorems/a1125452-7289-4972-a3bb-7b9be20047d7
-- title:
--   Proposition 4.2.3 — bounded levels of the conjugate representation
-- statement:
--   Let $\Phi:\mathbb R^L\to\mathbb R$ and the convex function $\phi:\mathbb R^M\to\mathbb R\cup\{+\infty\}$ be linked by
--   $$\Phi(w)=\sup_u\{\langle w,Au+a\rangle-\phi(u)\},$$
--   where $A$ is linear and $a\in\mathbb R^L$. Assume $\phi$ is lower semicontinuous and $A$ has trivial kernel. Then for every real $c$,
--   $$\{u:\phi(u)\le c\}\text{ is bounded}.$$
--
--   This supplies the bounded-level condition in Q.2 when the affine representation has an injective linear part.
--
--   **Formalization Note** Convexity and the exclusion of $-\infty$ are the standing function class surrounding (4.2.7). Lower semicontinuity is expressed by closed real sublevel sets; injectivity expresses trivial kernel. No boundedness assumption is placed on the effective domain.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Proposition 4.2.3, printed p. 85 (PDF p. 111)

import Definitions.Def_RobustOpt2009_Bernstein_Setup

open Set

namespace RobustOpt2009.Bernstein

theorem proposition_4_2_3 {L M : ℕ} (d : Setup L M)
    (hbot : ∀ u, d.phi u ≠ ⊥)
    (hconv : Convex ℝ {p : Space M × ℝ | d.phi p.1 ≤ (p.2 : EReal)})
    (hrep : representation d.Phi d.phi d.A d.a)
    (hlsc : ∀ c, IsClosed (sublevel d.phi c))
    (hinj : Function.Injective d.A) :
    ∀ c : ℝ, Bornology.IsBounded (sublevel d.phi c) := by sorry

end RobustOpt2009.Bernstein
