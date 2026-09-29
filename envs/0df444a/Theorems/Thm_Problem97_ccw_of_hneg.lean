-- Prove2me | Theorems.Thm_Problem97_ccw_of_hneg
-- name    : Problem97.ccw_of_hneg
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:04:08.55815+00:00
-- url     : https://prove2.me/theorems/7cbb4bda-b6ad-44c0-b08f-76a3be61d919
-- title:
--   Negative signed areas certify counterclockwise convex order
-- statement:
--   Let $\psi:\{0,\ldots,n-1\}\to\mathbb R^2$ be injective. If every triple with $i<j<k$ has negative doubled signed area under the repository's convention, then $\psi$ is a counterclockwise convex-polygon enumeration. This is the reverse conversion needed when cap constructions first establish signed-area inequalities.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_ccw_of_hneg.lean#L1-L110

/- Generated theorem stub from Erdos9796Proof.P97.ConvexCyclicOrder.Basic by Stage 2 proof cut; source SHA-256 f1ec282e547e3f3ca8edca05b96111ec2591b61f6aeecd11c668396d093955a1 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
open Problem97




/-!
# Convex cyclic order wrapper around `IsCcwConvexPolygon`

This module supplies a thin wrapper around the upstream predicate
`EuclideanGeometry.IsCcwConvexPolygon` (from
`FormalConjecturesForMathlib.Geometry.2d`) suited to the Nivasch–Pach–Pinchasi–Zerbib 2013
Lemma 6 sign-stability arguments consumed downstream by the CGN counting
bridge.

The key downstream consumer needs the statement "four points
`p, q, r, s` appear in this cyclic order on the convex-hull boundary
of `A`" plus an immediate algebraic API:

* `Problem97.ConvexCyclicOrder A p q r s` — the wrapper predicate.
* `oangle_sign_{pqr,qrs,pqs,prs}` — direct sign extraction for the
  four oriented angles whose central vertex is in the interior of
  the index sequence (immediate from `IsCcwConvexPolygon.sign_oangle`).
* `signedArea2_sign_stable_{pq, qr_chord}` — sign-stability of the
  `signedArea2` predicate as the third/first point varies along the
  cyclic order. Bridges via `signedArea2_sign_eq_oangle_sign` in
  `SignedAreaOangle`.

All proofs are mechanical composition of `IsCcwConvexPolygon.sign_oangle*`
with `signedArea2_sign_eq_oangle_sign`. No axioms are introduced.

## Step 1 scope

This file is the Step 1 wrapper.  It now includes the generic cyclic-shift
transport for `IsCcwConvexPolygon`, enough to change the linear cut of a
global boundary enumeration.  The higher-level
`ConvexCyclicOrder.rotate`/`ConvexCyclicOrder.reverse` wrapper API is still
deferred to Step 2.  Reversal flips chirality, so a faithful Step-2 reverse
should wrap upstream `IsConvexPolygon` (which already handles both
chiralities) rather than `IsCcwConvexPolygon`.
-/

open scoped EuclideanGeometry

theorem Problem97.ccw_of_hneg {n : ℕ} {ψ : Fin n → ℝ²}
    (hinj : Function.Injective ψ)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      signedArea2 (ψ i) (ψ j) (ψ k) < 0) :
    EuclideanGeometry.IsCcwConvexPolygon ψ := by sorry
