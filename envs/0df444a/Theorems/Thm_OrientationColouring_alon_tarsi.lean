-- Prove2me | Theorems.Thm_OrientationColouring_alon_tarsi
-- name    : OrientationColouring.alon_tarsi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:44.59322+00:00
-- url     : https://prove2.me/theorems/1ca0a6df-0238-4a0f-88dc-4b67b79c38a1
-- title:
--   Orientation Colouring: alon tarsi
-- statement:
--   **The Alon–Tarsi theorem (1992).** If an orientation `D` of `G` has different numbers of even
--   and odd Eulerian subdigraphs, then `G` can be properly coloured from any lists `L` with
--   `|L v|` larger than the out-degree of `v` in `D`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/Solution.lean#L39-L43
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/Solution.lean#L39-L43

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_AlonTarsi
public import Definitions.Def_AlonTarsiChoosability_Solution
public import Theorems.Thm_AlonTarsi_alon_tarsi

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open OrientationColouring
open AlonTarsi
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical

theorem OrientationColouring.alon_tarsi {Color : Type*} (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (hEO : eulerianCount D 0 ≠ eulerianCount D 1)
    (L : V → Finset Color) (hL : ∀ v, #{w | D v w} < (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by sorry
