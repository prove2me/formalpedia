-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_32
-- name    : TFIMPhaseDiagram.Classical.prop_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:04:02.290038+00:00
-- url     : https://prove2.me/theorems/45c6e457-d9cd-408d-82f2-09306ab856c0
-- title:
--   Proposition 32 — Dimension-free Gibbs perturbation in trace norm
-- statement:
--   For Hermitian complex matrices $K,C\in\mathbb C^{d\times d}$ with $d\ge1$,
--   $$\left\|\frac{e^{K+C}}{\operatorname{Tr}(e^{K+C})}-\frac{e^K}{\operatorname{Tr}(e^K)}\right\|_1\le\|C\|_{\rm op}.$$
--   The norm on the left is the Schatten-1 norm and on the right the Euclidean operator norm. The bound has no dimension factor and supplies the Gibbs perturbation input to the additive Trotter result.
--
--   Differences from the source:
--   - encoding: Schatten trace norm and operator norm → sum of singular values and supremum of the Euclidean matrix action; reason: These are the same norms; d>=1 excludes only the undefined empty Gibbs normalization.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.27 = PDF p.27, Proposition 32

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 32, p.27: Schatten-1 on the left, Euclidean operator norm on the right. -/
theorem prop_32 (d : ℕ) (hd : 0 < d) (K C : Matrix (Fin d) (Fin d) ℂ)
    (hK : K.IsHermitian) (hC : C.IsHermitian) :
  schattenOne ((Matrix.trace (matrixExp (K+C)))⁻¹ • matrixExp (K+C) -
    (Matrix.trace (matrixExp K))⁻¹ • matrixExp K) ≤ euclideanOpNorm C := by sorry
end TFIMPhaseDiagram.Classical
