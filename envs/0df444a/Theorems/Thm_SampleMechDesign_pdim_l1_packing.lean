-- Prove2me | Theorems.Thm_SampleMechDesign_pdim_l1_packing
-- name    : SampleMechDesign.pdim_l1_packing
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-06T15:50:36.553798+00:00
-- url     : https://prove2.me/theorems/a7403f4f-6c07-4ea2-af2f-3388d162f471
-- title:
--   Pollard–Haussler packing bound: an $\varepsilon$-separated family in empirical $L^1$ of pseudo-dimension $\le d$ has $\log|P|\le 2d\log(5eB/\varepsilon)$
-- statement:
--   Let $G$ be a class of real functions on a set $X$ whose pseudo-dimension is at most $d\in\mathbb N$ (every tuple shattered by $G$ has length at most $d$). Let $S=(S_1,\dots,S_N)$ be a sample with $g(S_i)\in[0,B]$ for all $g\in G$ and all $i$, and let $0<\varepsilon\le B$. If $P\subseteq G$ is a finite family that is $\varepsilon$-separated in the empirical $L^1$ distance, i.e. $\frac1N\sum_{i=1}^N|f(S_i)-g(S_i)|>\varepsilon$ for all distinct $f,g\in P$, then
--
--   $$\log|P|\le 2d\,\log\frac{5eB}{\varepsilon}.$$
--
--   Role: the packing (hence covering) bound in terms of the pseudo-dimension that the parent (Theorem 3.8, Pollard/Dudley) feeds into Dudley's chaining bound to control the empirical Rademacher complexity of the class on the sample by $O(U\sqrt{\mathrm{Pdim}/N})$.
--
--   **Formalization Note**: the pseudo-dimension bound is encoded as in the parent (every shattered $m$-tuple has $m\le d$, with the Shatters definition of Mohri et al. Def. 11.4); the packing number is stated for an arbitrary finite separated subfamily $P$. Haussler's constant $2(2eB/\varepsilon)^d\ln(2eB/\varepsilon)$ form is replaced by the simpler (weaker) logarithmic form $2d\log(5eB/\varepsilon)$, which is what the parent needs.
-- source:
--   D. Haussler, Decision theoretic generalizations of the PAC model for neural net and other learning applications, Information and Computation 100 (1992) 78-150, Theorem 6, p. 100 (packing numbers of classes of pseudo-dimension d, after D. Pollard, Convergence of Stochastic Processes, Springer 1984, Ch. II, Lemma 25); used in Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, Theorem 3.8, p.10

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters

namespace SampleMechDesign

open FoundationsML.Regression

theorem pdim_l1_packing {X : Type*} {G : Set (X → ℝ)} {d : ℕ}
    (hd : ∀ (m : ℕ) (z : Fin m → X), Shatters G z → m ≤ d)
    {B : ℝ} {N : ℕ} (S : Fin N → X) (hB : ∀ g ∈ G, ∀ i, g (S i) ∈ Set.Icc 0 B)
    {ε : ℝ} (hε : 0 < ε) (hεB : ε ≤ B)
    (P : Finset (X → ℝ)) (hP : ∀ f ∈ P, f ∈ G)
    (hsep : ∀ f ∈ P, ∀ g ∈ P, f ≠ g → ε < (1 / (N : ℝ)) * ∑ i, |f (S i) - g (S i)|) :
    Real.log (P.card : ℝ) ≤ 2 * d * Real.log (5 * Real.exp 1 * B / ε) := by sorry

end SampleMechDesign
