-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_fact_16
-- name    : SYKFastMix.FastMixing.fact_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:01.958905+00:00
-- url     : https://prove2.me/theorems/51f36317-c600-48ce-93c7-68a488af5257
-- title:
--   Fact 16 — Banach equality and the homogeneous polynomial derivative bound
-- statement:
--   Let $n,r\ge1$ and $a\ge0$ be integers. For every symmetric real $r$-linear form $T:(\mathbb R^n)^r\to\mathbb R$,
--   $$\sup_{\|u_1\|=\cdots=\|u_r\|=1}|T(u_1,\ldots,u_r)|=\sup_{\|u\|=1}|T(u,\ldots,u)|.$$
--   Every homogeneous polynomial map $P:\mathbb R^n\to\mathbb R^a$ of degree $r$ also satisfies
--   $$\sup_{\|x\|=1}\|DP(x)\|\le r\sup_{\|x\|=1}\|P(x)\|.$$
--   All norms are Euclidean and $DP(x)$ is the actual Fréchet derivative with its induced norm. Both clauses are retained for arbitrary positive degree; they control the classical coefficient estimates.
--
--   Differences from the source:
--   - encoding: homogeneous polynomial maps and unit spheres in Euclidean spaces → diagonals of symmetric continuous multilinear maps, with positive domain dimension; reason: every homogeneous real polynomial has such a polarization; positive dimension is the source unit-sphere convention and prevents empty real suprema
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 33, Fact 16, Eqs. (A.1)–(A.2)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem fact_16 (n a r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  (∀ (T : ContinuousMultilinearMap ℝ (fun _ : Fin r => E n) ℝ),
    IsSymmetricForm T →
    sSup {v : ℝ | ∃ u : Fin r → E n, (∀ i, ‖u i‖ = 1) ∧ v = |T u|} =
      sSup {v : ℝ | ∃ u : E n, ‖u‖ = 1 ∧ v = |T (fun _ => u)|}) ∧
  (∀ (T : ContinuousMultilinearMap ℝ (fun _ : Fin r => E n) (E a)),
    IsSymmetricForm T →
    sSup {v : ℝ | ∃ x : E n, ‖x‖ = 1 ∧ v = ‖fderiv ℝ (diagonalPolynomial T) x‖} ≤
      (r : ℝ) * sSup {v : ℝ | ∃ x : E n, ‖x‖ = 1 ∧ v = ‖diagonalPolynomial T x‖}) := by sorry

end SYKFastMix.FastMixing
