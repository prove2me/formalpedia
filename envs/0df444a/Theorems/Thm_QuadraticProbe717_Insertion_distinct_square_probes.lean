-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_distinct_square_probes
-- name    : QuadraticProbe717.Insertion.distinct_square_probes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:21.063043+00:00
-- url     : https://prove2.me/theorems/caac5d76-50f9-48b8-af1d-842782d2ab39
-- title:
--   Observation 2.1 — distinct square probes
-- statement:
--   For a prime $n$ and an integer $k$ with $1\le k\le n/2$, the map
--   $$[k]\longrightarrow\mathbb Z/n\mathbb Z,\qquad a\longmapsto a^2$$
--   is injective. Thus no distinct pair in this prefix has zero square difference. This is supporting development, rather than an extra milestone.
--
--   Differences from the source:
--   - encoding: indices 0≤a<b<k and congruences modulo n → injectivity on Fin k with values in ZMod n and 2k≤n; reason: the two formulations express the same distinctness property
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Observation 2.1, p. 4 (PDF p. 4)

import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem distinct_square_probes (n : ℕ) (hn : n.Prime) (k : ℕ)
    (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    Function.Injective (fun a : Fin k => (a.val : ZMod n)^2) := by sorry

end QuadraticProbe717.Insertion
