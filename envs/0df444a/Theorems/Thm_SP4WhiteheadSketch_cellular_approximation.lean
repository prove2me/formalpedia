-- Prove2me | Theorems.Thm_SP4WhiteheadSketch_cellular_approximation
-- name    : SP4WhiteheadSketch.cellular_approximation
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T10:41:26.272901+00:00
-- url     : https://prove2.me/theorems/220073dd-b79d-5f4a-aba8-f42d8ac04424
-- title:
--   Cellular approximation theorem for maps between CW complexes
-- statement:
--   This is the cellular approximation theorem (胞腔逼近定理).
--
--   Any continuous map $f:X\to Y$ between CW complexes is homotopic to a cellular map $g:X\to Y$,
--   $$f\simeq g,\qquad g(X^{n})\subseteq Y^{n}\ \text{for all }n,$$
--   and the homotopy may be taken stationary on a subcomplex on which $f$ is already cellular.
--
--   In the proof of Whitehead's theorem this replaces the mapping cone $M_f$ of an arbitrary map by the mapping cone of a cellular map, so that $(M_f,X)$ becomes a CW pair and the compression lemma applies.  In the contractible case it produces a cellular self-map of $Y$ homotopic to the identity, which the compression lemma then compresses to a constant.
-- source:
--   同伦论(2) Whitehead定理与胞腔逼近, 知乎专栏 https://zhuanlan.zhihu.com/p/22412267564 (压缩引理、胞腔逼近定理、Whitehead 定理证明); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Proposition 4.8 (cellular approximation) and Theorem 4.5 (Whitehead).

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4WhiteheadSketch
import Definitions.Def_SP4WeakHomotopy

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap

open scoped ContinuousMap
open ContinuousMap

universe u v

namespace SP4WhiteheadSketch

/-- The cellular approximation theorem (胞腔逼近定理).

Every continuous map `f : X → Y` between CW complexes is homotopic to a cellular map `g`,
i.e. a map carrying the `n`-skeleton of `X` into the `n`-skeleton of `Y` for every `n`.
This is the input that lets the mapping cone `M_f` of an arbitrary map be replaced, up to
homotopy, by the mapping cone of a cellular map, so that `(M_f, X)` is a CW pair.  In the
contractible case it produces a cellular self-map of `Y` homotopic to the identity, which is
then compressed by the compression lemma. -/
theorem cellular_approximation
    (X : Type u) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) :
    ∃ g : C(X, Y), CellularMap g ∧ Homotopic f g := by
  sorry

end SP4WhiteheadSketch
