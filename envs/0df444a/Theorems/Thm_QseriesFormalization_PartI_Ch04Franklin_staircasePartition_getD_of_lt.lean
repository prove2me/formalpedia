-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04Franklin_staircasePartition_getD_of_lt
-- name    : QseriesFormalization.PartI.Ch04Franklin.staircasePartition_getD_of_lt
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:27:05.652257+00:00
-- url     : https://prove2.me/theorems/0b80a2b0-649f-4133-ad05-2ab4ab7abb5f
-- title:
--   Entries of the staircase partition $[n,n-1,\dots,1]$
-- statement:
--   The staircase partition of height $n$ is the list $[n,n-1,\dots,2,1]$. For natural numbers $r<n$ the entry in zero-indexed position $r$ is $n-r$:
--   $$\mathrm{staircasePartition}(n)[r]=n-r.$$
--   This is a small lemma about the staircase shape that appears in the Franklin-involution proof of Euler's pentagonal number theorem.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04_FranklinPentagonal.lean#L765-L780

import Definitions.Def_QseriesFormalization_Chapter04_FranklinPentagonal
import Mathlib

/-!
# Chapter 5 — Boson-Fermion correspondence (Chan §5) — **partial setup only**

⚠️  **AUX CHAPTER — chapter-main result OPEN; file also contains Ch4-style
combinatorial material (strict partitions, Franklin involution)**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22):

What's here:
- (lines ~7-39) Setup for Chan §5: `AdmissibleState`, `charge`, `energy`,
  `vacuum` — Borcherd's fermion-sea configurations.  These are the
  building blocks for Chan's third proof of JTP via fermionic vs bosonic
  evaluation of the partition function `Z(q,z)`.
- (lines ~41 onward) Strict-partition infrastructure used by Franklin's
  involution (`Chapter05_Franklin.lean`), which is Chan §4's combinatorial
  proof of Euler's pentagonal number theorem (NOT §5 content).

What is **not** here:
- Chan Theorem 5 (effectively Eq 5.2 = Eq 5.4 ⇒ JTP) — the fermionic
  evaluation `Z(q,z) = ∏ (1+zq^{n-1/2})(1+z^{-1}q^{n-1/2})`, the bosonic
  evaluation `Z(q,z) = (1/(q;q)_∞) · ∑_{n∈ℤ} z^n q^{n²/2}`, and the
  derivation that equating them gives JTP.  These are the chapter's
  actual main content and are NOT formalized.

So this file is a mix of "Ch5 setup definitions" and "Ch4 Franklin
infrastructure".  The Franklin work is solid.

**Update (2026-05-24)**: Chan §5's *main theorem* — the **Jacobi Triple
Product** — IS proved in the repository and re-exported as
`Pending.Ch05JTP.jacobi_triple_product` (= `Ch02.jacobiTripleProduct`).  The
*result* of §5 is thus available; only §5's specific *proof method*
(Boson–Fermion / fermionic Fock space, eqs 5.2 = 5.4) is not formalized — the
repo instead proves JTP via the Chan §3 finite-JTP limit.
-/

open QseriesFormalization
open QseriesFormalization.PartI
open QseriesFormalization.PartI.Ch04Franklin

theorem QseriesFormalization.PartI.Ch04Franklin.staircasePartition_getD_of_lt {n r : Nat} (hr : r < n) :
    (staircasePartition n).getD r 0 = n - r := by sorry
