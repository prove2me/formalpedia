-- Prove2me | Theorems.Thm_SpectralProjGrad_SPG1_projection_ratio_antitone
-- name    : SpectralProjGrad.SPG1.projection_ratio_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:50:46.56004+00:00
-- url     : https://prove2.me/theorems/0a2c6756-fff1-4c12-b2ee-afc82d6fdca9
-- title:
--   Lemma 2.2 (i): $s\mapsto\|P(x+sz)-x\|/s$ is nonincreasing
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be closed and convex and let $P$ be the orthogonal projection onto $\Omega$. For every $x\in\Omega$ and every $z\in\mathbb R^n$, the function
--
--   $$
--   h(s)=\frac{\|P(x+sz)-x\|}{s},\qquad s>0,
--   $$
--
--   is monotonically nonincreasing: $0<s\le s'$ implies $h(s')\le h(s)$.
--
--   Along the projection arc $s\mapsto P(x+sz)$, the distance travelled grows at most linearly in $s$, with a rate that can only decrease. Applied with $z=-g(x)$, it compares the lengths of the scaled projected gradients $g_s(x)$ for different $s$, which is the key to controlling the backtracking of SPG1.
--
--   **Formalization Note** The paper writes $h:[0,\infty)\to\mathbb R$ but gives the formula only for $s>0$ and never defines $h(0)$; the monotonicity is therefore stated on the open half-line $(0,\infty)$. The objective $f$ plays no role in this item.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 5, Lemma 2.2 (i) (from Bertsekas, Nonlinear Programming (1995), Lemma 2.3.1)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

namespace SpectralProjGrad.SPG1

/-- Lemma 2.2 (i): for `x ∈ Ω` and `z ∈ ℝⁿ`, the function `h(s) = ‖P(x + s z) - x‖ / s` is
monotonically nonincreasing on `s > 0` (the only values at which the paper defines it). -/
theorem projection_ratio_antitone {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) (z : EuclideanSpace ℝ (Fin n)) :
    AntitoneOn (fun s : ℝ => ‖P (x + s • z) - x‖ / s) (Set.Ioi 0) := by sorry

end SpectralProjGrad.SPG1
