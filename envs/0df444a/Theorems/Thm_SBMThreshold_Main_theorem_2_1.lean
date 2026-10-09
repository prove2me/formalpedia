-- Prove2me | Theorems.Thm_SBMThreshold_Main_theorem_2_1
-- name    : SBMThreshold.Main.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:52.511256+00:00
-- url     : https://prove2.me/theorems/3c1465fa-e98f-48b5-8081-b41fd420a6db
-- title:
--   Theorem 2.1, p. 3 — if s² > d, some estimator's overlap with the planted labelling of G(n, a/n, b/n) is a.a.s. ≥ ε > 0
-- statement:
--   Let $a,b>0$ be fixed, put $d=(a+b)/2$ and $s=(a-b)/2$, and suppose
--   $$
--   s^2>d .
--   $$
--   Then the clustering problem in $\mathcal G(n,a/n,b/n)$ is solvable as $n\to\infty$: there are an estimator $\hat\tau$, which sees only the graph $G$ and may use internal randomness, and an $\varepsilon>0$ such that
--   $$
--   \lim_{n\to\infty}\mathbb P\Bigl[\Bigl|\frac1n\sum_v\sigma_v\hat\tau_v\Bigr|\ge\varepsilon\Bigr]=1 ,
--   $$
--   where $\sigma$ is the planted labelling and the probability is over $(\sigma,G)\sim\mathcal G(n,a/n,b/n)$ and the estimator's randomness.
--
--   This settles the conjecture of Decelle, Krzakala, Moore and Zdeborová that $s^2=d$ is the threshold for detection in the sparse two-community block model; below it, detection is impossible (Mossel, Neeman and Sly, 2012).
--
--   **Formalization Note** "One can a.a.s. find a bisection whose correlation with the planted bisection is bounded away from 0" is read as: some estimator, depending on $n$ and the graph only, achieves overlap at least a fixed $\varepsilon>0$ with probability tending to one. The overlap carries an absolute value because the two communities are unlabelled. The planted labels are i.i.d., so "bisection" means a two-class labelling, as in the paper's own Theorem 2.9. The estimator is a probability distribution on labellings for each graph, which covers the paper's randomized algorithm. For $n\le\max(a,b)$ the model's weights are not probabilities; the statement is a limit and does not depend on finitely many $n$.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 3, Theorem 2.1 (overlap as in Theorem 2.9, p. 6)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
open Filter Topology

namespace SBMThreshold.Main

/-- Theorem 2.1 (p. 3): if `s² > d` then some estimator, which sees only the graph, outputs a
labelling whose overlap with the planted labelling is at least a fixed `ε > 0` a.a.s. -/
theorem theorem_2_1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hKS : dPar a b < sPar a b ^ 2) :
    ∃ τhat : (n : ℕ) → SimpleGraph (Fin n) → PMF (Fin n → Bool), ∃ ε : ℝ, 0 < ε ∧
      Tendsto (fun n : ℕ => detectProb n a b (τhat n) ε) atTop (𝓝 1) := by sorry

end SBMThreshold.Main
