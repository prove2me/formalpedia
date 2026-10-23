-- Prove2me | Theorems.Thm_RobustOpt2009_CQApproximation_arrow_psd
-- name    : RobustOpt2009.CQApproximation.arrow_psd
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:23.523057+00:00
-- url     : https://prove2.me/theorems/bb4b2658-2cc8-4c1f-9356-59ad4375f26b
-- title:
--   Lemma 6.3.3 — semidefinite representation of the Lorentz cone
-- statement:
--   For $u\in\mathbb R^k$ and $t\in\mathbb R$,
--   $$\operatorname{Arrow}(u,t)\succeq0\quad\Longleftrightarrow\quad\|u\|_2\le t.$$
--   Thus the Lorentz-cone constraint has the displayed semidefinite representation.
--
--   **Formalization Note** The scalar coordinate is first. The statement includes $k=0$, where both sides say $0\le t$. The Euclidean norm is used explicitly.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Lemma 6.3.3, printed p. 163 (PDF p. 189).

import Definitions.Def_RobustOpt2009_CQApproximation_Basic

namespace RobustOpt2009.CQApproximation

/-- Lemma 6.3.3, printed p. 163, PDF p. 189. -/
theorem arrow_psd {k : ℕ} (u : Fin k → ℝ) (t : ℝ) :
    (arrow u t).PosSemidef ↔
      ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin k))‖ ≤ t := by sorry

end RobustOpt2009.CQApproximation
