-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_hermite_discretization_budget
-- name    : QuantumLTF.Membership.Supplement.hermite_discretization_budget
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T23:22:21.820724+00:00
-- url     : https://prove2.me/theorems/555d67ee-740c-47f4-9dc1-0dd73f7fe994
-- title:
--   Theorem 5.2 discretization error budget with the printed constants
-- statement:
--   Let $n\ge0$, $D+1\ge0$, $M>0$, and $\eta>0$. Suppose
--
--   $$M\ge\frac{20736n^2(D+1)}{\eta^2},\qquad M\ge\frac{165888n}{\eta^4},\qquad M\ge\frac4\pi\log\frac{12\sqrt{2n}}{\eta}.$$
--
--   Then the numerical discretization error satisfies
--
--   $$24n\sqrt{\frac{D+1}{M}}+2\left(\frac{8n}{M}\right)^{1/4}+2\sqrt{2n}\,e^{-\pi M/4}\le\frac\eta2.$$
--
--   This is the error allocation in Eq. (161), with the printed constants from Theorem 5.2. The analytic coefficient-discretization estimate in Lemma 5.1 remains a separate result.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5.1, Theorem 5.2, Eq. (161), numerical use of Lemma 5.1.

import Mathlib

theorem QuantumLTF.Membership.Supplement.hermite_discretization_budget (n D M η : ℝ)
    (hn : 0 ≤ n) (hD : 0 ≤ D+1) (hM : 0 < M) (hη : 0 < η)
    (h1 : 20736*n^2*(D+1)/η^2 ≤ M)
    (h2 : 165888*n/η^4 ≤ M)
    (h3 : 4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ M) :
    24*n*Real.sqrt ((D+1)/M) + 2*(8*n/M)^(1/4:ℝ) +
      2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) ≤ η/2 := by sorry
