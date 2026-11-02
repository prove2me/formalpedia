-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_conformal_uv_profile
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.conformal_uv_profile
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:55:23.649403+00:00
-- url     : https://prove2.me/theorems/efbe799e-5db4-4e2f-85b4-206fe404d7d8
-- title:
--   Conformal boundary profile and its finite-order logarithmic expansion
-- statement:
--   Consider a regular rotational disk profile in the conformal reduced model, with boundary-cylinder radius $R>0$ and maximal depth $b>0$. Write $z(t)$ for the direct graph, $r(z)$ for its inverse, $x=1-t/R$, and $f(x)=z(R(1-x))/(2R\sqrt{x})$. The graphs satisfy the Euler–Lagrange equation of $\int r z^{-3}\sqrt{1+r'^2}\,dz$, the regular axis condition, and positive finite regulated area. Such regular disks exist for every $R>0$. There are universal functions $B_1,B_2,B_3$ of one real variable such that each disk has a coefficient $a_1\in\mathbb R$ with
--
--   $$
--   z(t)\sim2\sqrt{R}\sqrt{R-t},\qquad
--   f(x)=1+a_1x+\tfrac18x\log x+\sum_{j=0}^{2} B_{j+1}(a_1)x^2(\log x)^j+o(x^2),
--   $$
--
--   and
--
--   $$
--   r(z)=R-\frac{z^2}{4R}+O(z^4\log z).
--   $$
--
--   All limits approach the boundary from the physical interior. This identifies the local terms that control the conformal UV subtraction; it asserts no convergence of an infinite formal series.
--
--   **Formalization Note** The printed variable $1-R/t$ is corrected to $1-t/R$, as required by the real square root and the displayed ODE. The coordinate correction was independently checked against (3.8)–(3.10) and (3.14) in moderation round one.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 7, (3.8)–(3.11), (3.14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF pp.7--9, (3.8)--(3.11),(3.14): finite-order conformal boundary
asymptotics of the regular disk profile. The printed x=1-R/r is corrected to
x=1-r/R because (3.8),(3.9),(3.10),(3.14) require positive x in the interior.
The three second-order coefficients depend only on a1, and no convergence of
an infinite formal series is asserted. The coordinate correction is fixed by
these source equations. -/
theorem conformal_uv_profile :
    ∃ B1 B2 B3 : ℝ → ℝ,
      (∀ R : ℝ, 0 < R → ∃ b : ℝ, ∃ r : ℝ → ℝ, IsDisk .conformal R b r) ∧
      ∀ (R b : ℝ) (r : ℝ → ℝ), IsDisk .conformal R b r →
        (Tendsto (fun t => height r b t /
          (2 * Real.sqrt R * Real.sqrt (R - t)))
          (nhdsWithin R (Iio R)) (nhds 1)) ∧
        (∃ a1 : ℝ,
          Asymptotics.IsLittleO (nhdsWithin (0 : ℝ) (Ioi 0))
            (fun x => conformalF R b r x -
              (1 + a1 * x + x * Real.log x / 8 + B1 a1 * x ^ 2 +
                B2 a1 * x ^ 2 * Real.log x + B3 a1 * x ^ 2 * Real.log x ^ 2))
            (fun x => x ^ 2)) ∧
        Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Ioi 0))
          (fun z => r z - R + z ^ 2 / (4 * R))
          (fun z => z ^ 4 * Real.log z) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
