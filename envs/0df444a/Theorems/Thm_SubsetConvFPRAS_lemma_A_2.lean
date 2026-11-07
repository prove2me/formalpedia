-- Prove2me | Theorems.Thm_SubsetConvFPRAS_lemma_A_2
-- name    : SubsetConvFPRAS.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:53.010207+00:00
-- url     : https://prove2.me/theorems/03d09d4f-8fc5-4dea-9be8-f924ef85a8d9
-- title:
--   Lemma A.2 — finding supported sets that contain $C$ and avoid $O$, at every size, with $O(n^3)$ queries
-- statement:
--   Let $g_\omega(x)=\sum_{A\subseteq U}\omega(A)x^A$ be nonzero and log-concave with nonnegative coefficients, $n=|U|$. Given a value oracle for $\omega$, a set $A_0\in\operatorname{supp}\omega$, and disjoint $C,O\subseteq U$, there is one program of the arithmetic model, with constants, that on every run uses at most $C(n+1)^3$ queries and halts within polynomial work $C'(n+1)^{K'}$, and either
--
--   1. outputs $0$, and then no $A\in\operatorname{supp}\omega$ contains $C$ and avoids $O$; or
--   2. outputs $1$, and then for every size $k$ at which such a set exists, bitmap $3+k$ holds a set $A\in\operatorname{supp}\omega$ of size $k$ containing $C$ and avoiding $O$.
--
--   This supplies the starting sets of Theorem 1.6 after pinning the coordinates with $\alpha_u\in\{0,2\}$, and of every homogeneous layer.
--
--   **Formalization Note** Input: integer cell $0$ holds $n$; bitmaps $0,1,2$ hold $A_0,C,O$; the oracle is the first one, and the statement holds for every second oracle.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model, O(·) operations and oracle calls → one admissible program of the unit-cost real RAM, with the constant C chosen before the instance and work counted per executed instruction; reason: the paper's model (p.44); every instruction costs 1, which only adds to the count
--   - generalization: an algorithm using O(n³) queries → also: every run halts within polynomial work C'(n+1)^{K'}; reason: the proof's local search does polynomial arithmetic; a program that must halt needs some bound, and the page's query bound is kept as stated
--   - encoding: n³ → (n+1)³; reason: covers n = 0; within a factor 8 for n ≥ 1
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Lemma A.2, p.35 (proof p.37)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_SetWeights
import Definitions.Def_SubsetConvFPRAS_Machine

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Lemma A.2, p.35. Let `g_ω` be nonzero and log-concave with
nonnegative coefficients. Given a value oracle for `ω`, a set `A₀ ∈ supp ω` and disjoint `C, O ⊆ U`, an algorithm using
`O(n³)` queries certifies that no `A ∈ supp ω` contains `C` and avoids `O`, or finds such a set for every size at which one
exists.

**Formalization Note.** The input layout is `initSupport`. Output `0` is the certificate, output `1` means that bitmap
`3 + k` holds such a set of size `k` for each size `k` at which one exists. The page bounds the queries only: `C` bounds
them, and the run also halts within a polynomial `C' (n+1)^K'` of work. The factor `(n+1)` covers `n = 0`. The second oracle
is not used; the statement holds for every `ν`. -/
theorem lemma_A_2 :
    ∃ (P : Program) (C C' K' : ℕ), Admissible P ∧
      ∀ (n : ℕ) (ω ν : Finset (Fin n) → ℝ), (∀ S, 0 ≤ ω S) → IsLogConcave ω →
      ∀ (A₀ Cs Os : Finset (Fin n)), 0 < ω A₀ → Disjoint Cs Os →
        let W : ℕ := C' * (n + 1) ^ K'
        let Feasible : Finset (Fin n) → Prop := fun A => 0 < ω A ∧ Cs ⊆ A ∧ Disjoint A Os
        ∀ tape : ℕ → Bool,
          let st := run P ω ν (initSupport A₀ Cs Os) tape W
          st.queries ≤ C * (n + 1) ^ 3 ∧ st.work ≤ W ∧
          ((st.output = some 0 ∧ ∀ A, ¬ Feasible A) ∨
            (st.output = some 1 ∧ ∀ k : ℕ, (∃ A, Feasible A ∧ A.card = k) →
              Feasible (st.bitmap (3 + (k : ℤ))) ∧ (st.bitmap (3 + (k : ℤ))).card = k)) := by sorry

end SubsetConvFPRAS
