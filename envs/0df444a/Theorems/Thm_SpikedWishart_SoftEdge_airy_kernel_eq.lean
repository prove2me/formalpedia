-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_airy_kernel_eq
-- name    : SpikedWishart.SoftEdge.airy_kernel_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:39:13.724024+00:00
-- url     : https://prove2.me/theorems/e21a759c-f225-46c0-8506-ab1efbda1c3f
-- title:
--   §1.2.1, p. 1646, (11)–(12) — Ai″ = u·Ai, and the divided-difference Airy kernel equals ∫₀^∞ Ai(u+z)Ai(z+v)dz
-- statement:
--   Let $\mathrm{Ai}$ be the Airy function defined by the contour integral (10), and $A(u,v)=\int_0^\infty\mathrm{Ai}(u+z)\mathrm{Ai}(z+v)\,dz$ the Airy kernel in the form (12). Then:
--
--   1. $\mathrm{Ai}$ satisfies the Airy equation $\mathrm{Ai}''(u)=u\,\mathrm{Ai}(u)$ for every real $u$;
--   2. for all real $u\ne v$,
--   $$
--   \frac{\mathrm{Ai}(u)\mathrm{Ai}'(v)-\mathrm{Ai}'(u)\mathrm{Ai}(v)}{u-v}=\int_0^\infty\mathrm{Ai}(u+z)\,\mathrm{Ai}(z+v)\,dz .
--   $$
--
--   This is the statement that the two formulas (11) and (12) of the Airy kernel agree, so that the kernel of $F_0=\det(1-A_x)$, the GUE Tracy–Widom law, can be read in either form.
--
--   **Formalization Note** The identity is stated off the diagonal: in Lean $x/0=0$, so (11) carries a junk value on $u=v$, which is why the mission defines the kernel by (12).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1646, §1.2.1, (11)–(12)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy

namespace SpikedWishart.SoftEdge

theorem airy_kernel_eq :
    (∀ u : ℝ, deriv (deriv Ai) u = u * Ai u) ∧
      ∀ u v : ℝ, u ≠ v →
        (Ai u * deriv Ai v - deriv Ai u * Ai v) / (u - v) = airyKernel u v := by sorry

end SpikedWishart.SoftEdge
