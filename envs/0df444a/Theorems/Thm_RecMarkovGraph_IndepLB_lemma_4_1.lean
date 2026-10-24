-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_4_1
-- name    : RecMarkovGraph.IndepLB.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:35.136981+00:00
-- url     : https://prove2.me/theorems/65468edc-c154-437e-98ef-b56cd681b621
-- title:
--   Lemma 4.1, p. 9 — f_a(x) = x(1 − ax) is concave, unimodal with maximum 1/(4a), has no nonzero fixed point and f_a(x) < x
-- statement:
--   Let $a\in(0,1]$ and $f_a(x)=x(1-ax)$. Then $f_a$ is concave on $\mathbb R$ and:
--
--   1. $f_a$ is strictly increasing on $(-\infty,\tfrac1{2a}]$ and strictly decreasing on $(\tfrac1{2a},\infty)$;
--   2. $f_a(x)\le \tfrac1{4a}$ for all $x$, with equality at $x=\tfrac1{2a}$;
--   3. $f_a(x)=x$ only for $x=0$;
--   4. $f_a(x)\in(0,1)$ for $x\in(0,1)$;
--   5. $f_a(x)<x$ for $x\ne0$;
--   6. $a\,f_a(x)=f_1(ax)$ for all $x$;
--   7. $f_a(x)<f_b(x)$ for every $x>0$ and every real $b<a$.
--
--   These elementary facts drive the analysis of the recursion $x_{n+1}=f_a(x_n)$, which governs the edge probabilities of $G^r_{n,p}$ (with $a=\gamma$).
--
--   Differences from the source:
--   - reading: "is increasing on (−∞, 1/(2a)] and decreasing on (1/(2a), ∞)" → StrictMonoOn on Iic (1/(2a)) and StrictAntiOn on Ioi (1/(2a)); reason: the stronger of the two readings, true for a > 0
--   - encoding: "has a maximum value of 1/(4a)" → f_a(x) ≤ 1/(4a) for all x and f_a(1/(2a)) = 1/(4a); reason: the definition of a maximum value
--   - generalization: item 7 for a > b, with b a parameter of (3), i.e. b ∈ (0, 1] → every real b < a; reason: the inequality −a x² < −b x² holds for every real b < a; it specializes to b ∈ (0, 1]
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 9, Lemma 4.1 (proof in §9, p. 22); context (3), p. 9

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open Set

theorem lemma_4_1 (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ConcaveOn ℝ univ (fa a) ∧
    (StrictMonoOn (fa a) (Iic (1 / (2 * a))) ∧ StrictAntiOn (fa a) (Ioi (1 / (2 * a)))) ∧
    ((∀ x, fa a x ≤ 1 / (4 * a)) ∧ fa a (1 / (2 * a)) = 1 / (4 * a)) ∧
    (∀ x, fa a x = x → x = 0) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, fa a x ∈ Ioo (0 : ℝ) 1) ∧
    (∀ x, x ≠ 0 → fa a x < x) ∧
    (∀ x, a * fa a x = fa 1 (a * x)) ∧
    (∀ b x : ℝ, b < a → 0 < x → fa a x < fa b x) := by sorry

end RecMarkovGraph.IndepLB
