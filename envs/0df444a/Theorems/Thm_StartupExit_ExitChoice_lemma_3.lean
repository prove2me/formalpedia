-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_lemma_3
-- name    : StartupExit.ExitChoice.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:02.25267+00:00
-- url     : https://prove2.me/theorems/9ff8555f-f334-4c68-b998-530614cc7b90
-- title:
--   Lemma 3, p. 12 — for uniform values: X(1, z) = (z−1)/(z+1), X(2, z) = (z−3)/(z+1), (1/z)[X(1, z) − X(2, z)] = 2/(z(z+1))
-- statement:
--   Let $X(1,z)$ and $X(2,z)$ be the expected highest and second-highest of $z$ independent uniform draws on $[-1,1]$, computed as $\int_{-1}^1 x f(x,z)\,dx$ and $\int_{-1}^1 x g(x,z)\,dx$ with the densities of Lemma 1. Then
--
--   $$X(1,z)=\frac{z-1}{z+1}\quad(z\ge1),\qquad X(2,z)=\frac{z-3}{z+1},\qquad \frac1z\bigl[X(1,z)-X(2,z)\bigr]=\frac{2}{z(z+1)}\quad(z\ge2).$$
--
--   These closed forms turn every profit in the model into an explicit function of $w,m,n$; for instance eq. (3) for $\tilde\theta$ follows from them.
--
--   **Formalization Note** The page states the lemma for $z$ buyers without a range. The second-highest of $z$ draws needs $z\ge2$ (at $z=1$ the density $g(\cdot,1)$ vanishes and the integral is $0$, not $-1$), so the $X(2,\cdot)$ and $\pi_B$ parts are stated for $z\ge2$ and the $X(1,\cdot)$ part for $z\ge1$.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), p. 12 (PDF 13), Lemma 3

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_OrderStats

namespace StartupExit.ExitChoice

theorem lemma_3 :
    (∀ z : ℕ, 1 ≤ z → X1 z = ((z : ℝ) - 1) / ((z : ℝ) + 1)) ∧
    (∀ z : ℕ, 2 ≤ z → X2 z = ((z : ℝ) - 3) / ((z : ℝ) + 1) ∧
      (1 / (z : ℝ)) * (X1 z - X2 z) = 2 / ((z : ℝ) * ((z : ℝ) + 1))) := by sorry

end StartupExit.ExitChoice
