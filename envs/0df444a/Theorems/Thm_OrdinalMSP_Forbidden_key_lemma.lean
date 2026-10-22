-- Prove2me | Theorems.Thm_OrdinalMSP_Forbidden_key_lemma
-- name    : OrdinalMSP.Forbidden.key_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:35.963014+00:00
-- url     : https://prove2.me/theorems/cf01013f-a5da-45ad-9718-634c13aa4fe8
-- title:
--   Lemma 1 (Key Lemma), p. 9 — with p = p(k), every algorithm with forbidden sets of size k is α(k) probability-competitive
-- statement:
--   Let $\mathcal M$ be a matroid on a finite ground set $R$, $|R| = n$, totally ordered by the value order $\succ$, and let $\mathrm{OPT}$ be its greedy (lexicographically optimum) base. Let $k \ge 1$ and let $\mathrm{ALG}$ be an algorithm with forbidden sets of size $k$ (Definition 7). Set the sampling probability to $p = p(k)$, so that the sample size is $s \sim \mathrm{Bin}(n, p(k))$, independent of a uniformly random arrival order, where
--   $$(p(k),\ \alpha(k)) = \begin{cases} (1/e,\ e) & \text{if } k = 1,\\ (k^{-\frac{1}{k-1}},\ k^{\frac{k}{k-1}}) & \text{if } k \ge 2.\end{cases}$$
--   Then $\mathrm{ALG}$ is $\alpha(k)$ probability-competitive: for every $r^* \in \mathrm{OPT}$,
--   $$\Pr(r^* \in \mathrm{ALG}) \ \ge\ \frac{1}{\alpha(k)}.$$
--
--   This is the Key Lemma of Soto, Turkieltaub and Verdugo: it reduces the design of constant probability-competitive algorithms for the ordinal matroid secretary problem to exhibiting forbidden sets of constant size. The paper applies it to obtain, among others, ratio $e$ for transversal matroids, $4$ for graphic matroids, $3\sqrt3$ for laminar matroids and $k^{k/(k-1)}$ for $k$-framed matroids.
--
--   **Formalization Note** The probability is the exact finite sum over sample sizes $s = 0, \dots, n$ with weights $\binom ns p^s(1-p)^{n-s}$ and over the $n!$ equally likely arrival orders (Setting definition). The algorithm is an arbitrary map from (arrival order, sample size) to an output set satisfying the three properties of Definition 7; online-ness is not required and internal randomness beyond $s$ is not modelled. The matroid's ground set is all of $R$; the value order is Lean's `<` read upward; $e$ is `Real.exp 1` and the powers are `Real.rpow`.
-- source:
--   Soto, Turkieltaub & Verdugo, Strong Algorithms for the Ordinal Matroid Secretary Problem, arXiv:1802.01997v1, Lemma 1 (Key Lemma), p. 9 (first stated p. 4)

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

namespace OrdinalMSP.Forbidden

theorem key_lemma {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (hE : M.E = Set.univ) (k : ℕ) (hk : 1 ≤ k)
    (ALG : ArrivalOrder R → ℕ → Finset R) (hALG : HasForbiddenSets M k ALG) :
    IsProbCompetitive M ALG (pK k) (alphaK k) := by sorry

end OrdinalMSP.Forbidden
