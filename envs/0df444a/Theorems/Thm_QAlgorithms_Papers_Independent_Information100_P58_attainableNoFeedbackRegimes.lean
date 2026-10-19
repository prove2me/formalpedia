-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_attainableNoFeedbackRegimes
-- name    : QAlgorithms.Papers.Independent.Information100.P58.attainableNoFeedbackRegimes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:20:38.201894+00:00
-- url     : https://prove2.me/theorems/50699c9d-fd41-406e-a5b0-33d0b040e77b
-- title:
--   No-feedback regimes attaining the dimension bound
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For $M\ge1$ equiprobable messages, write $s_{n,d,p}(M)=\sum_{k=0}^n b_k\min\{1,d^k/M\}$. The following deterministic classical constructions, decoded by uniform guessing among compatible messages, have average success $P_{\rm succ}(C)$ satisfying
--
--   $$P_{\rm succ}(C)=s_{n,d,p}(M).$$
--
--   1. If $M\le d$, there exists an attaining code that repeats a single symbol in all $n$ positions.
--   2. If $M\ge d^n$, there exists a code containing every length-$n$ word, and every such exhaustive code attains the bound, with repetitions permitted.
--   3. If $0\le r\le n$, $M=d^r$, and a given code projects bijectively onto every $r$-coordinate set, it attains the bound. Its projections onto fewer coordinates are surjective, and those onto more coordinates are injective.
--
--   The last conclusion is conditional on the projection property; such codes are not asserted to exist for arbitrary parameters. Only average-success attainment is claimed.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 26, Remark 6.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Remark 6.3, PDF p.26: repetition, exhaustive word lists, and conditional MDS projection attainability. -/
theorem attainableNoFeedbackRegimes (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    (M≤d → ∃ C : Fin M → Word n d, Function.Injective C ∧ (∀ m i j, C m i = C m j) ∧
      deterministicAverage p C = dimensionSuccess n d p M) ∧
    (d^n≤M → (∃ C : Fin M → Word n d, Function.Surjective C ∧
      deterministicAverage p C = dimensionSuccess n d p M) ∧
      ∀ C : Fin M → Word n d, Function.Surjective C →
      deterministicAverage p C = dimensionSuccess n d p M) ∧
    (∀ r : ℕ, r≤n → M=d^r → ∀ C : Fin M → Word n d,
      (∀ S : Finset (Fin n), S.card=r →
        Function.Bijective (fun m => fun i : {i : Fin n // i∈S} => C m i.val)) →
      deterministicAverage p C = dimensionSuccess n d p M ∧
      (∀ S : Finset (Fin n), S.card≤r → Function.Surjective
        (fun m => fun i : {i : Fin n // i∈S} => C m i.val)) ∧
      (∀ S : Finset (Fin n), r≤S.card → Function.Injective
        (fun m => fun i : {i : Fin n // i∈S} => C m i.val))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
