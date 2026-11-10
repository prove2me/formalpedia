-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_proposition_3_3
-- name    : UnconditionalKLS.Dunkl.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:39.121871+00:00
-- url     : https://prove2.me/theorems/9a2ae5d6-b0c2-409e-afc6-247da6825047
-- title:
--   Proposition 3.3 — parity, sign, and spectral lower bound
-- statement:
--   Let $n\ge1$, $S>0$, and let $W$ satisfy (2.4). For the auxiliary law $\eta$ and its Rayleigh gap $\lambda$, the gap is positive and finite. There are a coordinate $i$ and an operator-domain function $f$ such that
--   $$Af=\lambda f,\quad\mathbb E_\eta f^2=1,\quad R_if=-f,\quad R_jf=f\ (j\ne i),\quad x_if\ge0\quad\eta\text{-a.e.}$$
--   For these same witnesses the moment $\mathbb E_\eta[X_if]$ is finite and strictly positive, the expression below is integrable, and
--   $$\lambda\ge\frac3{S^2}\Longrightarrow\lambda\ge\left(\frac{\mathbb E_\eta[c_i]}{2\mathbb E_\eta[X_if]^2}\mathbb E_\eta\!\left[\frac{c_iW_if^2}{X_i^3}\right]\right)^{1/3}.$$
--   Here $R_jf=f\circ r_j$ and $W_i=\partial_iW$. All parity identities concern the same normalized eigenfunction in $L^2(\eta)$. This selects the parity and sign information needed for the spectral estimate without assuming eigenfunction smoothness.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
--   - encoding: first nonzero eigenvalue and the nonzero denominator in (3.7) → positive finite gap, integrability and strictly positive coordinate moment are explicit conclusions; reason: the source’s normalization and sign together with Gaussian tails justify these; no denominator or regularity property is assumed
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 17, Proposition 3.3; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem proposition_3_3 {n : ℕ} (hn : 0 < n) (S : ℝ) (W : Fn n)
    (hS : 0 < S) (hW : Admissible W) :
    0 < gap S W ∧ gap S W < ⊤ ∧
    ∃ (i : Fin n) (f : Fn n), OperatorDomain S W f ∧
      action S W f = (gap S W).toReal • l2 (eta S W) f ∧
      (∫ x, (f x)^2 ∂eta S W) = 1 ∧ OneOdd (eta S W) f i ∧
      (∀ᵐ x ∂eta S W, 0 ≤ x i * f x) ∧
      Integrable (fun x => x i * f x) (eta S W) ∧
      0 < (∫ x, x i * f x ∂eta S W) ∧
      Integrable (fun x => cj S i x * d W i x * (f x)^2 / (x i)^3) (eta S W) ∧
      (3 / S^2 ≤ (gap S W).toReal →
        Real.rpow ((∫ x, cj S i x ∂eta S W) *
          (∫ x, cj S i x * d W i x * (f x)^2 / (x i)^3 ∂eta S W) /
          (2 * (∫ x, x i * f x ∂eta S W)^2)) (1/3 : ℝ) ≤ (gap S W).toReal) := by sorry
end UnconditionalKLS.Dunkl
