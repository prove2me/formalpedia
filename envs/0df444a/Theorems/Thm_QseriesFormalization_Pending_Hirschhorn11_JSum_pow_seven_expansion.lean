-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Hirschhorn11_JSum_pow_seven_expansion
-- name    : QseriesFormalization.Pending.Hirschhorn11.JSum_pow_seven_expansion
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:31:57.030251+00:00
-- url     : https://prove2.me/theorems/690ea239-0ccf-4ab8-8e42-911e5024b79e
-- title:
--   Multinomial expansion of $(J_0+J_1+J_3+J_6+J_{10})^7$ over $\mathbb{Z}/11$
-- statement:
--   In $(\mathbb{Z}/11)[[X]]$, with $J_i$ the residue-$i$ mod 11 component of $(q;q)_\infty^3$ and `JSum` $=J_0+J_1+J_3+J_6+J_{10}$, the seventh power is written out as the sum of the 330 multinomial terms $C\,J_0^aJ_1^bJ_3^cJ_6^dJ_{10}^e$ (each as `JTerm`) with $a+b+c+d+e=7$ and $C$ the multinomial coefficient. A bookkeeping lemma for Hirschhorn's mod 11 proof (Chapter 17).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter17_Hirschhorn_Mod11.lean#L409-L497

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

theorem QseriesFormalization.Pending.Hirschhorn11.JSum_pow_seven_expansion :
    JSum ^ 7 =
      JTerm 1 7 0 0 0 0 + JTerm 7 6 1 0 0 0 + JTerm 7 6 0 1 0 0 + JTerm 7 6 0 0 1 0
      + JTerm 7 6 0 0 0 1 + JTerm 21 5 2 0 0 0 + JTerm 42 5 1 1 0 0 + JTerm 42 5 1 0 1 0
      + JTerm 42 5 1 0 0 1 + JTerm 21 5 0 2 0 0 + JTerm 42 5 0 1 1 0 + JTerm 42 5 0 1 0 1
      + JTerm 21 5 0 0 2 0 + JTerm 42 5 0 0 1 1 + JTerm 21 5 0 0 0 2 + JTerm 35 4 3 0 0 0
      + JTerm 105 4 2 1 0 0 + JTerm 105 4 2 0 1 0 + JTerm 105 4 2 0 0 1 + JTerm 105 4 1 2 0 0
      + JTerm 210 4 1 1 1 0 + JTerm 210 4 1 1 0 1 + JTerm 105 4 1 0 2 0 + JTerm 210 4 1 0 1 1
      + JTerm 105 4 1 0 0 2 + JTerm 35 4 0 3 0 0 + JTerm 105 4 0 2 1 0 + JTerm 105 4 0 2 0 1
      + JTerm 105 4 0 1 2 0 + JTerm 210 4 0 1 1 1 + JTerm 105 4 0 1 0 2 + JTerm 35 4 0 0 3 0
      + JTerm 105 4 0 0 2 1 + JTerm 105 4 0 0 1 2 + JTerm 35 4 0 0 0 3 + JTerm 35 3 4 0 0 0
      + JTerm 140 3 3 1 0 0 + JTerm 140 3 3 0 1 0 + JTerm 140 3 3 0 0 1 + JTerm 210 3 2 2 0 0
      + JTerm 420 3 2 1 1 0 + JTerm 420 3 2 1 0 1 + JTerm 210 3 2 0 2 0 + JTerm 420 3 2 0 1 1
      + JTerm 210 3 2 0 0 2 + JTerm 140 3 1 3 0 0 + JTerm 420 3 1 2 1 0 + JTerm 420 3 1 2 0 1
      + JTerm 420 3 1 1 2 0 + JTerm 840 3 1 1 1 1 + JTerm 420 3 1 1 0 2 + JTerm 140 3 1 0 3 0
      + JTerm 420 3 1 0 2 1 + JTerm 420 3 1 0 1 2 + JTerm 140 3 1 0 0 3 + JTerm 35 3 0 4 0 0
      + JTerm 140 3 0 3 1 0 + JTerm 140 3 0 3 0 1 + JTerm 210 3 0 2 2 0 + JTerm 420 3 0 2 1 1
      + JTerm 210 3 0 2 0 2 + JTerm 140 3 0 1 3 0 + JTerm 420 3 0 1 2 1 + JTerm 420 3 0 1 1 2
      + JTerm 140 3 0 1 0 3 + JTerm 35 3 0 0 4 0 + JTerm 140 3 0 0 3 1 + JTerm 210 3 0 0 2 2
      + JTerm 140 3 0 0 1 3 + JTerm 35 3 0 0 0 4 + JTerm 21 2 5 0 0 0 + JTerm 105 2 4 1 0 0
      + JTerm 105 2 4 0 1 0 + JTerm 105 2 4 0 0 1 + JTerm 210 2 3 2 0 0 + JTerm 420 2 3 1 1 0
      + JTerm 420 2 3 1 0 1 + JTerm 210 2 3 0 2 0 + JTerm 420 2 3 0 1 1 + JTerm 210 2 3 0 0 2
      + JTerm 210 2 2 3 0 0 + JTerm 630 2 2 2 1 0 + JTerm 630 2 2 2 0 1 + JTerm 630 2 2 1 2 0
      + JTerm 1260 2 2 1 1 1 + JTerm 630 2 2 1 0 2 + JTerm 210 2 2 0 3 0 + JTerm 630 2 2 0 2 1
      + JTerm 630 2 2 0 1 2 + JTerm 210 2 2 0 0 3 + JTerm 105 2 1 4 0 0 + JTerm 420 2 1 3 1 0
      + JTerm 420 2 1 3 0 1 + JTerm 630 2 1 2 2 0 + JTerm 1260 2 1 2 1 1 + JTerm 630 2 1 2 0 2
      + JTerm 420 2 1 1 3 0 + JTerm 1260 2 1 1 2 1 + JTerm 1260 2 1 1 1 2 + JTerm 420 2 1 1 0 3
      + JTerm 105 2 1 0 4 0 + JTerm 420 2 1 0 3 1 + JTerm 630 2 1 0 2 2 + JTerm 420 2 1 0 1 3
      + JTerm 105 2 1 0 0 4 + JTerm 21 2 0 5 0 0 + JTerm 105 2 0 4 1 0 + JTerm 105 2 0 4 0 1
      + JTerm 210 2 0 3 2 0 + JTerm 420 2 0 3 1 1 + JTerm 210 2 0 3 0 2 + JTerm 210 2 0 2 3 0
      + JTerm 630 2 0 2 2 1 + JTerm 630 2 0 2 1 2 + JTerm 210 2 0 2 0 3 + JTerm 105 2 0 1 4 0
      + JTerm 420 2 0 1 3 1 + JTerm 630 2 0 1 2 2 + JTerm 420 2 0 1 1 3 + JTerm 105 2 0 1 0 4
      + JTerm 21 2 0 0 5 0 + JTerm 105 2 0 0 4 1 + JTerm 210 2 0 0 3 2 + JTerm 210 2 0 0 2 3
      + JTerm 105 2 0 0 1 4 + JTerm 21 2 0 0 0 5 + JTerm 7 1 6 0 0 0 + JTerm 42 1 5 1 0 0
      + JTerm 42 1 5 0 1 0 + JTerm 42 1 5 0 0 1 + JTerm 105 1 4 2 0 0 + JTerm 210 1 4 1 1 0
      + JTerm 210 1 4 1 0 1 + JTerm 105 1 4 0 2 0 + JTerm 210 1 4 0 1 1 + JTerm 105 1 4 0 0 2
      + JTerm 140 1 3 3 0 0 + JTerm 420 1 3 2 1 0 + JTerm 420 1 3 2 0 1 + JTerm 420 1 3 1 2 0
      + JTerm 840 1 3 1 1 1 + JTerm 420 1 3 1 0 2 + JTerm 140 1 3 0 3 0 + JTerm 420 1 3 0 2 1
      + JTerm 420 1 3 0 1 2 + JTerm 140 1 3 0 0 3 + JTerm 105 1 2 4 0 0 + JTerm 420 1 2 3 1 0
      + JTerm 420 1 2 3 0 1 + JTerm 630 1 2 2 2 0 + JTerm 1260 1 2 2 1 1 + JTerm 630 1 2 2 0 2
      + JTerm 420 1 2 1 3 0 + JTerm 1260 1 2 1 2 1 + JTerm 1260 1 2 1 1 2 + JTerm 420 1 2 1 0 3
      + JTerm 105 1 2 0 4 0 + JTerm 420 1 2 0 3 1 + JTerm 630 1 2 0 2 2 + JTerm 420 1 2 0 1 3
      + JTerm 105 1 2 0 0 4 + JTerm 42 1 1 5 0 0 + JTerm 210 1 1 4 1 0 + JTerm 210 1 1 4 0 1
      + JTerm 420 1 1 3 2 0 + JTerm 840 1 1 3 1 1 + JTerm 420 1 1 3 0 2 + JTerm 420 1 1 2 3 0
      + JTerm 1260 1 1 2 2 1 + JTerm 1260 1 1 2 1 2 + JTerm 420 1 1 2 0 3 + JTerm 210 1 1 1 4 0
      + JTerm 840 1 1 1 3 1 + JTerm 1260 1 1 1 2 2 + JTerm 840 1 1 1 1 3 + JTerm 210 1 1 1 0 4
      + JTerm 42 1 1 0 5 0 + JTerm 210 1 1 0 4 1 + JTerm 420 1 1 0 3 2 + JTerm 420 1 1 0 2 3
      + JTerm 210 1 1 0 1 4 + JTerm 42 1 1 0 0 5 + JTerm 7 1 0 6 0 0 + JTerm 42 1 0 5 1 0
      + JTerm 42 1 0 5 0 1 + JTerm 105 1 0 4 2 0 + JTerm 210 1 0 4 1 1 + JTerm 105 1 0 4 0 2
      + JTerm 140 1 0 3 3 0 + JTerm 420 1 0 3 2 1 + JTerm 420 1 0 3 1 2 + JTerm 140 1 0 3 0 3
      + JTerm 105 1 0 2 4 0 + JTerm 420 1 0 2 3 1 + JTerm 630 1 0 2 2 2 + JTerm 420 1 0 2 1 3
      + JTerm 105 1 0 2 0 4 + JTerm 42 1 0 1 5 0 + JTerm 210 1 0 1 4 1 + JTerm 420 1 0 1 3 2
      + JTerm 420 1 0 1 2 3 + JTerm 210 1 0 1 1 4 + JTerm 42 1 0 1 0 5 + JTerm 7 1 0 0 6 0
      + JTerm 42 1 0 0 5 1 + JTerm 105 1 0 0 4 2 + JTerm 140 1 0 0 3 3 + JTerm 105 1 0 0 2 4
      + JTerm 42 1 0 0 1 5 + JTerm 7 1 0 0 0 6 + JTerm 1 0 7 0 0 0 + JTerm 7 0 6 1 0 0
      + JTerm 7 0 6 0 1 0 + JTerm 7 0 6 0 0 1 + JTerm 21 0 5 2 0 0 + JTerm 42 0 5 1 1 0
      + JTerm 42 0 5 1 0 1 + JTerm 21 0 5 0 2 0 + JTerm 42 0 5 0 1 1 + JTerm 21 0 5 0 0 2
      + JTerm 35 0 4 3 0 0 + JTerm 105 0 4 2 1 0 + JTerm 105 0 4 2 0 1 + JTerm 105 0 4 1 2 0
      + JTerm 210 0 4 1 1 1 + JTerm 105 0 4 1 0 2 + JTerm 35 0 4 0 3 0 + JTerm 105 0 4 0 2 1
      + JTerm 105 0 4 0 1 2 + JTerm 35 0 4 0 0 3 + JTerm 35 0 3 4 0 0 + JTerm 140 0 3 3 1 0
      + JTerm 140 0 3 3 0 1 + JTerm 210 0 3 2 2 0 + JTerm 420 0 3 2 1 1 + JTerm 210 0 3 2 0 2
      + JTerm 140 0 3 1 3 0 + JTerm 420 0 3 1 2 1 + JTerm 420 0 3 1 1 2 + JTerm 140 0 3 1 0 3
      + JTerm 35 0 3 0 4 0 + JTerm 140 0 3 0 3 1 + JTerm 210 0 3 0 2 2 + JTerm 140 0 3 0 1 3
      + JTerm 35 0 3 0 0 4 + JTerm 21 0 2 5 0 0 + JTerm 105 0 2 4 1 0 + JTerm 105 0 2 4 0 1
      + JTerm 210 0 2 3 2 0 + JTerm 420 0 2 3 1 1 + JTerm 210 0 2 3 0 2 + JTerm 210 0 2 2 3 0
      + JTerm 630 0 2 2 2 1 + JTerm 630 0 2 2 1 2 + JTerm 210 0 2 2 0 3 + JTerm 105 0 2 1 4 0
      + JTerm 420 0 2 1 3 1 + JTerm 630 0 2 1 2 2 + JTerm 420 0 2 1 1 3 + JTerm 105 0 2 1 0 4
      + JTerm 21 0 2 0 5 0 + JTerm 105 0 2 0 4 1 + JTerm 210 0 2 0 3 2 + JTerm 210 0 2 0 2 3
      + JTerm 105 0 2 0 1 4 + JTerm 21 0 2 0 0 5 + JTerm 7 0 1 6 0 0 + JTerm 42 0 1 5 1 0
      + JTerm 42 0 1 5 0 1 + JTerm 105 0 1 4 2 0 + JTerm 210 0 1 4 1 1 + JTerm 105 0 1 4 0 2
      + JTerm 140 0 1 3 3 0 + JTerm 420 0 1 3 2 1 + JTerm 420 0 1 3 1 2 + JTerm 140 0 1 3 0 3
      + JTerm 105 0 1 2 4 0 + JTerm 420 0 1 2 3 1 + JTerm 630 0 1 2 2 2 + JTerm 420 0 1 2 1 3
      + JTerm 105 0 1 2 0 4 + JTerm 42 0 1 1 5 0 + JTerm 210 0 1 1 4 1 + JTerm 420 0 1 1 3 2
      + JTerm 420 0 1 1 2 3 + JTerm 210 0 1 1 1 4 + JTerm 42 0 1 1 0 5 + JTerm 7 0 1 0 6 0
      + JTerm 42 0 1 0 5 1 + JTerm 105 0 1 0 4 2 + JTerm 140 0 1 0 3 3 + JTerm 105 0 1 0 2 4
      + JTerm 42 0 1 0 1 5 + JTerm 7 0 1 0 0 6 + JTerm 1 0 0 7 0 0 + JTerm 7 0 0 6 1 0
      + JTerm 7 0 0 6 0 1 + JTerm 21 0 0 5 2 0 + JTerm 42 0 0 5 1 1 + JTerm 21 0 0 5 0 2
      + JTerm 35 0 0 4 3 0 + JTerm 105 0 0 4 2 1 + JTerm 105 0 0 4 1 2 + JTerm 35 0 0 4 0 3
      + JTerm 35 0 0 3 4 0 + JTerm 140 0 0 3 3 1 + JTerm 210 0 0 3 2 2 + JTerm 140 0 0 3 1 3
      + JTerm 35 0 0 3 0 4 + JTerm 21 0 0 2 5 0 + JTerm 105 0 0 2 4 1 + JTerm 210 0 0 2 3 2
      + JTerm 210 0 0 2 2 3 + JTerm 105 0 0 2 1 4 + JTerm 21 0 0 2 0 5 + JTerm 7 0 0 1 6 0
      + JTerm 42 0 0 1 5 1 + JTerm 105 0 0 1 4 2 + JTerm 140 0 0 1 3 3 + JTerm 105 0 0 1 2 4
      + JTerm 42 0 0 1 1 5 + JTerm 7 0 0 1 0 6 + JTerm 1 0 0 0 7 0 + JTerm 7 0 0 0 6 1
      + JTerm 21 0 0 0 5 2 + JTerm 35 0 0 0 4 3 + JTerm 35 0 0 0 3 4 + JTerm 21 0 0 0 2 5
  + JTerm 7 0 0 0 1 6 + JTerm 1 0 0 0 0 7 := by sorry
