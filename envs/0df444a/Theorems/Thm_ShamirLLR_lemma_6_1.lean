-- Prove2me | Theorems.Thm_ShamirLLR_lemma_6_1
-- name    : ShamirLLR.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:50.132115+00:00
-- url     : https://prove2.me/theorems/2f78997f-0b9f-4fb8-85ef-58c7ef5b0d03
-- title:
--   Lemma 6.1 — uniform short moment certificate
-- statement:
--   Fix $b>0$ and a positive integer $D$, and put $q=\lceil 4D/b\rceil$. There is $C_{b,D}>0$, depending only on $b,D$, such that for all sufficiently large $m$ (in terms of $b,D$), every $bm\le r<m$ and every $B\ge2$, with $H=(2B)^{C_{b,D}}$: for each integer array $C=(C_i)_{i=1}^m$, $C_i\in\mathbb Z^{q\times D}$, of height at most $B$ one can choose, using $C$ alone, a nonzero $u_C\in\mathbb Z^q$ with
--   $$
--   qB\|u_C\|_\infty\le H ,
--   $$
--   and for every prime $p>\max\{H,(mD)!B^{mD},m(m+1)\}$, except on an event of probability at most
--   $$
--   \frac{2Dm(r-1)(2B+1)^{qmD}}{p}
--   $$
--   over $a\in\mathcal A_{p,m}$, the implication
--   $$
--   \Bigl[\sum_{i=1}^m a_i^hC_ix_i=0\ (0\le h<r)\Bigr]\Longrightarrow u_C^{\top}C_ix_i=0\ (i\in[m])
--   $$
--   holds simultaneously for every such array and every $x_i\in\mathbb F_p^D$.
--
--   This is where the randomness of the evaluation places enters: one good event works for all arrays and solutions chosen after $a$ is known.
--
--   Differences from the source:
--   - reading: "one can choose a nonzero $u_C$, using $C$ alone"; "Fix the assignment $C\mapsto u_C$ before sampling $a$" → a map $u$ on arrays chosen after $m, r, B$ and before $p$ and $a$; reason: the printed order of quantifiers and p.40
--   - encoding: "$m$ sufficiently large in terms of $b, D$" → $m\ge M_0$ for some $M_0$ chosen with $C_{b,D}$; reason: both depend only on $b, D$
--   - encoding: probability over uniform $a\in\mathcal A_{p,m}$ → proportion of tuples in $\mathcal A_{p,m}$ at which the simultaneous implication fails; reason: uniform distribution
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 6.1, Eq. (36)–(39), pp.39–40; §6.1, p.39 (PDF pp.40–41)

import Mathlib
import Definitions.Def_ShamirLLR_evalTuples

set_option autoImplicit false

open Matrix

namespace ShamirLLR

open Classical in
/-- **Lemma 6.1 (Uniform short moment certificate).** Fix `b > 0` and `D ∈ ℕ`, and put
`q = ⌈4D/b⌉`. Let `bm ≤ r < m`, with `m` sufficiently large in terms of `b, D`. For every `B ≥ 2`
there is a bound `H = (2B)^{C_{b,D}}`, where `C_{b,D} > 0` depends only on `b, D`, with the
following property. Suppose `p > max{H, (mD)! B^{mD}, m(m + 1)}` (36). For each integer array
`C = (C_i)_{i=1}^m`, `C_i ∈ ℤ^{q×D}`, of height at most `B`, one can choose a nonzero
`u_C ∈ ℤ^q`, using `C` alone, such that `qB‖u_C‖_∞ ≤ H` (37). Except on an event of probability
at most `2Dm(r − 1)(2B + 1)^{qmD}/p` (38) over `a ∈ A_{p,m}`, the implication
`[∑_i a_i^h C_i x_i = 0 (0 ≤ h < r)] ⇒ u_C^⊺ C_i x_i = 0 (i ∈ [m])` (39) holds simultaneously
for every such array and every choice of `x_i ∈ 𝔽_p^D`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Lemma 6.1, Eq. (36)–(39), pp.39–40; §6.1, p.39.

**Formalization Note.** `D` is a positive integer ("Fix a positive real number b and a positive
integer D", §6.1, p.39). The certificate is a map `u` on arrays, chosen after `m, r, B` and before
`p` and `a` ("Fix the assignment C ↦ u_C before sampling a", p.40). The height of an array is
its largest absolute entry; integer entries are reduced mod `p` in the moment equations. The
probability is the proportion of `a ∈ A_{p,m}` at which the simultaneous implication fails. -/
theorem lemma_6_1 (b : ℝ) (hb : 0 < b) (D : ℕ) (hD : 1 ≤ D) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → ∀ r : ℕ, b * m ≤ r → r < m →
      ∀ B : ℝ, 2 ≤ B →
        ∃ u : (Fin m → Matrix (Fin ⌈4 * D / b⌉₊) (Fin D) ℤ) → (Fin ⌈4 * D / b⌉₊ → ℤ),
          (∀ C : Fin m → Matrix (Fin ⌈4 * D / b⌉₊) (Fin D) ℤ, (∀ i j k, (|C i j k| : ℝ) ≤ B) →
            u C ≠ 0 ∧ ∀ j, (⌈4 * D / b⌉₊ : ℝ) * B * |(u C j : ℝ)| ≤ (2 * B) ^ Cb) ∧
          ∀ (p : ℕ) [Fact p.Prime],
            max ((2 * B) ^ Cb) (max (((m * D).factorial : ℝ) * B ^ (m * D)) ((m : ℝ) * (m + 1)))
              < p →
            (((evalTuples p m).filter (fun a => ¬ ∀ C : Fin m → Matrix (Fin ⌈4 * D / b⌉₊) (Fin D) ℤ,
                (∀ i j k, (|C i j k| : ℝ) ≤ B) → ∀ x : Fin m → Fin D → ZMod p,
                  (∀ h : ℕ, h < r →
                    ∑ i, a i ^ h • ((C i).map (Int.cast : ℤ → ZMod p) *ᵥ x i) = 0) →
                  ∀ i, (fun j => ((u C j : ℤ) : ZMod p)) ⬝ᵥ
                    ((C i).map (Int.cast : ℤ → ZMod p) *ᵥ x i) = 0)).card : ℝ) /
                (evalTuples p m).card ≤
              2 * D * m * ((r : ℝ) - 1) * (2 * B + 1) ^ (⌈4 * D / b⌉₊ * m * D) / p := by sorry

end ShamirLLR
