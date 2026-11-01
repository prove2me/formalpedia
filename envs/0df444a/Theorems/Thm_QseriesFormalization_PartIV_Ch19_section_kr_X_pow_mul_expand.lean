-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_section_kr_X_pow_mul_expand
-- name    : QseriesFormalization.PartIV.Ch19.section_kr_X_pow_mul_expand
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:59:52.425127+00:00
-- url     : https://prove2.me/theorems/5622e7a9-4fc1-4a41-8f89-9cf561365d39
-- title:
--   Section recovers $\varphi$ from $X^r\varphi(X^k)$
-- statement:
--   Let $R$ be a commutative ring, $k\ne0$, $r<k$ and $\varphi\in R[[X]]$. Then
--   $$\mathrm{section}_{k,r}\big(X^r\,\varphi(X^k)\big)=\varphi,$$
--   where `section_kr` $R\,k\,r\,\psi=\sum_n[X^{kn+r}]\psi\,X^n$ and $\varphi(X^k)$ is `PowerSeries.expand`. It lets one extract the residue-$r$ part of series of this shape; Chapter 19.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_Section5.lean#L80-L104

import Definitions.Def_QseriesFormalization_Chapter19_Section5
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

/-!
# Chapter 19 — k-sections of power series (foundation for MBI / general Ramanujan)

To prove `∀ n, 5 ∣ p(5n+4)` and the other Ramanujan congruence families
unconditionally, we need Hirschhorn-style algebra on (ZMod p)⟦X⟧ that
extracts the coefficients in a fixed residue class.  The natural tool is
the **k-section operator** at residue r:

  section_kr φ := mk (fun n => coeff φ (k·n + r))

This file defines that operator and proves its basic algebraic properties.
These are foundation lemmas for the MBI proof (Pending/Chapter16_MBI.lean)
and for discharging the formal-PS vanishing hypothesis needed by Chapter
19's `ramanujan_from_pochInf_vanishes`.

All theorems in this file are unconditional (no sorry, no axiom beyond
the core three).
-/

open QseriesFormalization
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch19

open PowerSeries

theorem QseriesFormalization.PartIV.Ch19.section_kr_X_pow_mul_expand
    (R : Type*) [CommRing R] (k : ℕ) (hk : k ≠ 0) (r : ℕ) (hr : r < k)
    (φ : PowerSeries R) :
    section_kr R k r ((PowerSeries.X (R := R)) ^ r *
        PowerSeries.expand k hk φ) = φ := by sorry
