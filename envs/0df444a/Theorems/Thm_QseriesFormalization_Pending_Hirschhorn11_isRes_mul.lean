-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Hirschhorn11_isRes_mul
-- name    : QseriesFormalization.Pending.Hirschhorn11.isRes_mul
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T11:32:37.850369+00:00
-- url     : https://prove2.me/theorems/e22dd3a8-2aab-4a42-b2c4-1679b18622a3
-- title:
--   Residue supports mod 11 add under multiplication
-- statement:
--   Let $R$ be a commutative ring, $r,s\in\mathbb{N}$, and $f,g\in R[[X]]$. For $t\in\mathbb{N}$ and $h\in R[[X]]$, write $S_{11}(t,h)$ for the condition $$\forall n\in\mathbb{N},\quad n\bmod 11\ne t\ \Longrightarrow\ [X^n]h=0.$$ If $S_{11}(r,f)$ and $S_{11}(s,g)$, then $$S_{11}\big((r+s)\bmod 11,fg\big).$$ The remainder is compared with $t$ literally: when $t\ge 11$, $S_{11}(t,h)$ forces $h=0$. For $t<11$ it is the usual residue-support condition.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean#L182 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_Pending_Chapter17_Hirschhorn_Mod11
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 17 — Hirschhorn's elementary proof of `∀ n, 11 ∣ p(11n + 6)`

Following Hirschhorn (2014), *J. Number Theory* **139**, 205–209, and
*The Power of q* (Springer 2017) §3.5.

**Strategy** (entirely in `ZMod 11` formal power series):

1. Decompose `(qPoch ZMod 11)^3` into 11-residue parts `J_0, J_1, J_3, J_6, J_{10}`:
   By B2 (Jacobi cube identity) `(qPoch)^3 = ∑ (-1)^k (2k+1) X^{T_k}`.
   `T_k mod 11 ∈ {0, 1, 3, 6, 10}` after excluding `k ≡ 5 mod 11` (where the
   coefficient `2k+1 ≡ 0 mod 11`).
   Hence `(qPoch ZMod 11)^3 = J_0 + J_1 + J_3 + J_6 + J_10` where `J_i` keeps
   only terms with exponent `≡ i (mod 11)`.

2. Frobenius lift: `1/(qPoch ZMod 11) = (qPoch)^{21}/(qPoch)^{22}`.
   `(qPoch)^{22} = ((qPoch)^{11})^2 = (expand 11 qPoch)^2` (Frobenius).
   `(qPoch)^{21} = ((qPoch)^3)^7 = (J_0+J_1+J_3+J_6+J_{10})^7`.
   So `partitionGenFun ZMod 11 ≡ (J_0+J_1+J_3+J_6+J_{10})^7 / (expand 11 qPoch ZMod 11)^2`.

3. Extract coefficient of `X^{11n+6}` from LHS = `partitionCount (11n+6) mod 11`.
   From RHS = sum P of `J_a J_b J_c J_d J_e J_f J_g` monomials with total
   exponent ≡ 6 mod 11, divided by `(expand 11 qPoch)^2`.

4. **Key trick** (Hirschhorn): `(J_0+J_1+J_3+J_6+J_{10})^4 = ((qPoch)^3)^4 =
   (qPoch)^{12} = (qPoch)^{11} · qPoch ≡ (expand 11 qPoch) · qPoch (mod 11)`.

5. `(expand 11 qPoch) · qPoch` has non-zero coefficients only at exponents whose
   mod-11 residue is in `{pentagonal mod 11} = {0, 1, 2, 4, 5, 7}`.
   So residues `{3, 6, 8, 9, 10}` give zero coefficient.

6. Equating with LHS expansion of `(J_0+J_1+J_3+J_6+J_{10})^4`, we get 5 polynomial
   relations among `J_i`-monomials (one for each forbidden residue).

7. Hirschhorn shows the residue-6 monomial sum `P` (after the 7th-power expansion)
   is a `Z`-linear combination of these 5 relations with explicit multipliers
   `a = 7, b = 5, c = 7`.  Hence `P ≡ 0 (mod 11)`.

**This file is a SCAFFOLD with intermediate sorries**.  The structure is set
up; closing each step is concrete algebraic work but requires writing out the
30+ monomial expansion explicitly.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.Hirschhorn11

open PowerSeries
open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.Pending.Hirschhorn11.isRes_mul {R : Type*} [CommRing R] {r s : ℕ} {φ ψ : R⟦X⟧}
    (hφ : IsRes r φ) (hψ : IsRes s ψ) :
    IsRes ((r + s) % 11) (φ * ψ) := by sorry
