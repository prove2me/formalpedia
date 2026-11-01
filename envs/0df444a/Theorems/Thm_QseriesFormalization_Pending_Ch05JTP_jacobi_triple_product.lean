-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch05JTP_jacobi_triple_product
-- name    : QseriesFormalization.Pending.Ch05JTP.jacobi_triple_product
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:44:35.418165+00:00
-- url     : https://prove2.me/theorems/fc4e9fb1-ff40-4a7f-bc1f-a85027a2f2f2
-- title:
--   Jacobi triple product: $\prod_{n\ge1}(1-q^{2n})(1+zq^{2n-1})(1+z^{-1}q^{2n-1})=\sum_{n\in\mathbb{Z}}z^nq^{n^2}$
-- statement:
--   For complex $q,z$ with $\|q\|<1$ and $z\ne0$,
--   $$\prod_{n\ge1}(1-q^{2n})(1+zq^{2n-1})(1+z^{-1}q^{2n-1})=\sum_{n\in\mathbb{Z}}z^nq^{n^2},$$
--   with the product as a Lean `tprod` and the bilateral series as a `tsum`. This is the Jacobi triple product, the main theorem of Chapter 5 (re-exported from the Chapter 2 proof).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 5. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter05_JTP.lean#L34-L42

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib

/-!
# Chapter 5 — the Jacobi Triple Product (Chan §5's main result)

Chan §5 ("Borcherds' proof of the Jacobi Triple Product" / Boson–Fermion
correspondence) has as its **main result the Jacobi Triple Product identity
(JTP)** itself; §5 gives a particular proof of it via the Boson–Fermion
correspondence (eqs 5.2 + 5.4).

The repository's `Chapter05*.lean` files instead contain **Franklin's
involution** (a combinatorial proof of Euler's pentagonal number theorem,
Chan §4 material), so the audit marks `Chapter05.lean` MISLABELED.

This file records that **Chan §5's main theorem — the JTP — IS proved in this
repository**, namely as `QseriesFormalization.PartI.Ch02.jacobiTripleProduct`:

  for `‖q‖ < 1` and `z ≠ 0`,
  `∏_{n≥1} (1 - q^{2n})(1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})  =  ∑_{n ∈ ℤ} zⁿ q^{n²}`.

The proof used here is the **finite-JTP limit** (Chan §3 route), **not** the
Boson–Fermion correspondence of Chan §5.  So the *theorem* of §5 is available;
the specific §5 *proof method* (vertex-operator / fermionic Fock space) is not
formalized.
-/

open QseriesFormalization

open QseriesFormalization.PartI.Ch02

theorem QseriesFormalization.Pending.Ch05JTP.jacobi_triple_product (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    jacobiInfiniteProduct q z = jacobiInfiniteSeries q z := by sorry
