-- Prove2me | Theorems.Thm_QuantumScalingMWPM_QLiquidationist_lemma_12
-- name    : QuantumScalingMWPM.QLiquidationist.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:16:07.062836+00:00
-- url     : https://prove2.me/theorems/3f407561-60d3-4640-a375-7cb5f21fab01
-- title:
--   Lemma 12 — no eligible augmenting path after the augmentation task
-- statement:
--   Let $M$ be a matching of $G$, $\Omega$ a valid blossom family for $M$, $y$ vertex duals and $w$ integer weights. Consider any terminating run of Algorithm 1 on $(G,w,M,y,\Omega)$ with output $\Psi$, all GROVERSEARCH calls correct. Let $M_2$ be the matching obtained by augmenting $M$ along the lifts to $G$ of the paths of $\Psi$; this is the augmentation task, Task 2.
--
--   Then there is no eligible augmenting path of blossoms in $G/\Omega$ with respect to $M_2$. Equivalently, there is no augmenting path of root blossoms of $\Omega$ all of whose edges satisfy Criterion 2 for $M_2$ and $y$.
--
--   This is the precondition of Task 3: when the ordered search is run again on $M_2$, its augmenting-path branch is never taken.
--
--   Differences from the source:
--   - encoding: conditioned on the correctness of all calls to GROVERSEARCH → a nondeterministic transition system in which each GROVERSEARCH call returns some marked neighbour, and ⊥ exactly when none exists; the statement holds for every run; reason: this is the conditioning: every correct resolution of every call
--   - generalization: Algorithm 1 enumerates the free vertices (line 8) and the vertices of a blossom (foreach x ∈ V(B)) in an unspecified order → any order of the free vertices, and any enumeration order ord of each blossom (ValidOrd ord); reason: the source fixes no order; the statement for every order specializes to whatever order an implementation uses
--   - reading: the standing blossom invariant of §2.1 (p. 6: maintained "so that these facts always hold"; App. E, p. 39), not printed in the statement → hypotheses: M is a matching of G and Ω is a valid blossom family for M (IsBlossomFamily); reason: every call of the procedure in the source is made on such a structure; without it the objects of the statement (bases, blossom cycles) are undefined
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Lemma 12, p. 21 (the argument of [13], Lemma 2.3, cited p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch

namespace QuantumScalingMWPM.QLiquidationist

variable {n : ℕ}

/-- Lemma 12 (p. 21). After the augmentation task (augmenting `M` along the lifts of the paths
returned by Algorithm 1) there is no eligible augmenting path in `G/Ω`. -/
theorem lemma_12 (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Ω : Family n) (ord : Finset (Fin n) → List (Fin n))
    (hM : IsMatching G M) (hΩ : IsBlossomFamily G M Ω) (hord : ValidOrd ord)
    (s : Alg1State n) (hs : Alg1Final G w M y Ω ord s) :
    ∀ P, ¬ IsEligAugPathH G w (augmentAll M (s.psi.map (liftG Ω))) y Ω P := by sorry

end QuantumScalingMWPM.QLiquidationist
