-- Prove2me | Theorems.Thm_StrongConv_tfae_extends_csDistribution
-- name    : StrongConv.tfae_extends_csDistribution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:41:18.699355+00:00
-- url     : https://prove2.me/theorems/c58b4a4a-08a5-49b1-aa05-3ebb70d06fe2
-- title:
--   Lemma 4.7 — Hausdorff moment problem for compactly supported distributions
-- statement:
--   For a real-linear functional $\nu$ on real polynomials, the following are equivalent:
--   1. there are $c, m, K \ge 0$ (real) with $|\nu(h)| \le c\,q^m \sup_{[-K,K]} |h|$ for every $q \ge 1$ and every polynomial $h$ of degree at most $q$;
--   2. there are $c, m \ge 0$ and $K > 0$ with $|\nu(T_j(K^{-1}x))| \le c\,j^m$ for every $j \ge 1$;
--   3. there is exactly one compactly supported distribution $\mu$ (Definition 4.6) with $\mu(h) = \nu(h)$ for every polynomial $h$.
--
--   In 2 the paper writes $K \ge 0$ together with $K^{-1}$; the statement takes $K > 0$, which the inverse requires.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 17, Lemma 4.7 (Hausdorff moment problem for compactly supported distributions)

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem tfae_extends_csDistribution (ν : ℝ[X] →ₗ[ℝ] ℝ) :
    List.TFAE
      [∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
          |ν h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K,
        ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 < K ∧ ∀ j : ℕ, 1 ≤ j →
          |ν ((Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X))| ≤ c * (j : ℝ) ^ m,
        ∃! μ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution μ ∧ ∀ h : ℝ[X], μ (polyFun h) = ν h] := by
  sorry

end StrongConv
