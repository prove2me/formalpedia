-- Prove2me | Theorems.Thm_TitiusBode_dermott_geometric_spacing
-- name    : TitiusBode.dermott_geometric_spacing
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:31.111001+00:00
-- url     : https://prove2.me/theorems/23d61ad9-3e3e-43a7-9c77-fc51d6fdc205
-- title:
--   Dermott's law — geometric periods and Titius–Bode-type geometric distances
-- statement:
--   Let $T(n) = T(0)\,C^n$ be Dermott's law with $T(0) > 0$ and $C > 0$, and let $K$ be any real constant. Then for every $n$:
--
--   1. consecutive periods have constant ratio: $T(n+1)/T(n) = C$;
--   2. the Keplerian semi-major axes $a(n) = K\,T(n)^{2/3}$ form a geometric progression with ratio $C^{2/3}$:
--   $$a(n+1) = C^{2/3}\, a(n).$$
--
--   The Dermott article presents its law as a power law of the same kind as the Titius–Bode law, and the Titius–Bode article (section "Natural satellite systems and exoplanetary systems") calls it a "slight new phrasing" of that law; this milestone records the precise relationship between the period law and a geometric distance law.
--
--   **Formalization Note** The statement holds for all $n \ge 0$; the source indexes satellites by $n = 1, 2, 3, \dots$.
-- source:
--   Wikipedia, "Dermott's law", revision oldid=1315813288, https://en.wikipedia.org/w/index.php?title=Dermott%27s_law&oldid=1315813288; Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, section "Natural satellite systems and exoplanetary systems" and footnote 1 (semi-major axis proportional to the 2/3 power of the period)

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology

namespace TitiusBode
theorem dermott_geometric_spacing (T₀ C K : ℝ) (hT₀ : 0 < T₀) (hC : 0 < C) (n : ℕ) :
    dermottPeriod T₀ C (n + 1) / dermottPeriod T₀ C n = C ∧
    K * dermottPeriod T₀ C (n + 1) ^ ((2 : ℝ) / 3) =
      C ^ ((2 : ℝ) / 3) * (K * dermottPeriod T₀ C n ^ ((2 : ℝ) / 3)) := by sorry
end TitiusBode
