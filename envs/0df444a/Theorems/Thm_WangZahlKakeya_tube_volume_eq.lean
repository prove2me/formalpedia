-- Prove2me | Theorems.Thm_WangZahlKakeya_tube_volume_eq
-- name    : WangZahlKakeya.tube_volume_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T15:04:02.538789+00:00
-- url     : https://prove2.me/theorems/0a7bc257-f4cd-4cf7-abd6-0e255091c2ac
-- title:
--   All $\delta$-tubes have the same volume $|T|$
-- statement:
--   **The volume of a $\delta$-tube does not depend on its position or its direction.**
--
--   For every base point $p \in \mathbb{R}^3$, every unit vector $v$ and every $\delta$, the $\delta$-neighbourhood of the segment from $p$ to $p+v$ has the same Lebesgue measure as the reference tube along the first coordinate axis:
--
--   $$\bigl|\,\mathrm{tube}(p,v,\delta)\,\bigr| \;=\; |T| .$$
--
--   This is the statement implicit in the notation of the source, where $|T|$ denotes *the* volume of a $\delta$-tube: any two $\delta$-tubes are isometric, and Lebesgue measure on $\mathbb{R}^3$ is invariant under isometries. It is what allows the density of a shading to be compared with the single quantity $(\#\mathbb{T})|T|$, and in particular it forces $\lambda \le 1$ for a $\lambda$-dense system.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 5, the conventions of §1.2 preceding Definition 1.3 (“$|T|$ will denote the volume of a $\delta$-tube”)

import Definitions.Def_WangZahlKakeya_wolff
open MeasureTheory Metric Set

namespace WangZahlKakeya

theorem tube_volume_eq (p v : E3) (δ : ℝ) (hv : ‖v‖ = 1) :
    (volume (tube p v δ)).toReal = tubeVol δ := by sorry

end WangZahlKakeya
