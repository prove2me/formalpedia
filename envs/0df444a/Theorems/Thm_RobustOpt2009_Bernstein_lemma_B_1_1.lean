-- Prove2me | Theorems.Thm_RobustOpt2009_Bernstein_lemma_B_1_1
-- name    : RobustOpt2009.Bernstein.lemma_B_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:24.560971+00:00
-- url     : https://prove2.me/theorems/e7e995e0-cf7d-43c3-b527-d3bae2a161ae
-- title:
--   Lemma B.1.1 — closure of a homogenized convex sublevel set
-- statement:
--   Let $H:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous and convex. Let $a\in\mathbb R$ satisfy $H(0)>a$, assume $0\in\operatorname{int}\operatorname{dom}H$, and assume $\{z:H(z)<a\}$ is nonempty. Define $H^o=\{z:\exists\beta>0,\ H(\beta^{-1}z)\le a\}$ and $\mathcal H=\operatorname{cl}H^o$. Then
--   $$G(z)=\inf_{\beta>0}\bigl[\beta H(\beta^{-1}z)-\beta a\bigr]$$
--   is finite everywhere and convex,
--   $$\mathcal H=\{z:G(z)\le0\},$$
--   and $\mathcal H$ is a nonempty closed convex cone.
--
--   This is the appendix's closure and perspective characterization used in the Bernstein approximation.
--
--   **Formalization Note** Extended-real convexity is convexity of the real epigraph; lower semicontinuity is closedness of every real sublevel set. Finiteness of the extended-real infimum is a conclusion, not an assumption.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Lemma B.1.1, printed p. 471 (PDF p. 497)

import Definitions.Def_RobustOpt2009_Bernstein_Setup

open Set

namespace RobustOpt2009.Bernstein

theorem lemma_B_1_1 {n : ℕ} (H : Space n → EReal) (a : ℝ)
    (hbot : ∀ z, H z ≠ ⊥)
    (hconv : Convex ℝ {p : Space n × ℝ | H p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ c, IsClosed (sublevel H c))
    (hzero : (a : EReal) < H 0)
    (hdom : (0 : Space n) ∈ interior {z | H z < ⊤})
    (hstrict : ∃ z, H z < (a : EReal)) :
    (∀ z, ∃ r : ℝ, perspectiveValue H a z = (r : EReal)) ∧
    Convex ℝ {p : Space n × ℝ | perspectiveValue H a p.1 ≤ (p.2 : EReal)} ∧
    closure (initialCone H a) = {z | perspectiveValue H a z ≤ 0} ∧
    (closure (initialCone H a)).Nonempty ∧
    IsClosed (closure (initialCone H a)) ∧ Convex ℝ (closure (initialCone H a)) ∧
    (0 : Space n) ∈ closure (initialCone H a) ∧
    (∀ z ∈ closure (initialCone H a), ∀ t : ℝ, 0 ≤ t →
      t • z ∈ closure (initialCone H a)) := by sorry

end RobustOpt2009.Bernstein
